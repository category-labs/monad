#pragma once

#include <memory>

#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/result.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/lru/static_lru_cache.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/find_request_sender.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

MONAD_MPT_NAMESPACE_BEGIN

struct OnDiskDbConfig;
struct ReadOnlyOnDiskDbConfig;
struct StateMachine;
struct TraverseMachine;
struct AsyncContext;

class Db
{
private:
    friend struct AsyncContext;

    struct Impl;
    struct RWOnDisk;
    struct ROOnDisk;
    struct InMemory;

    std::unique_ptr<Impl> impl_;

public:
    Db(StateMachine &); // In-memory mode
    Db(StateMachine &, OnDiskDbConfig const &);
    Db(ReadOnlyOnDiskDbConfig const &);

    Db(Db const &) = delete;
    Db(Db &&) = delete;
    Db &operator=(Db const &) = delete;
    Db &operator=(Db &&) = delete;
    ~Db();

    // May wait on a fiber future
    //  The `block_id` parameter is used for version control validation
    Result<NodeCursor> find(NodeCursor, NibblesView, uint64_t block_id) const;
    Result<NodeCursor> find(NibblesView prefix, uint64_t block_id) const;
    Result<byte_string_view> get(NibblesView, uint64_t block_id) const;
    Result<byte_string_view> get_data(NibblesView, uint64_t block_id) const;
    Result<byte_string_view>
    get_data(NodeCursor, NibblesView, uint64_t block_id) const;

    NodeCursor load_root_for_version(uint64_t block_id) const;

    void copy_trie(
        uint64_t src_version, NibblesView src, uint64_t dest_version,
        NibblesView dest, bool blocked_by_write = true);

    void upsert(
        UpdateList, uint64_t block_id, bool enable_compaction = true,
        bool can_write_to_fast = true, bool write_root = true);

    void update_finalized_block(uint64_t);
    void update_verified_block(uint64_t);
    uint64_t get_latest_finalized_block_id() const;
    uint64_t get_latest_verified_block_id() const;

    // Traverse APIs: return value indicates if we have finished the full
    // traversal or not.
    // Parallel traversal is a single threaded out of order traverse using async
    // i/o. Note that RWDb impl waits on a fiber future, therefore any parallel
    // traverse run on RWDb should not do any blocking i/o because that will
    // block the fiber and hang. If you have to do blocking i/o during the
    // traversal on RWDb, use the `traverse_blocking` api below.
    bool traverse(
        NodeCursor, TraverseMachine &, uint64_t block_id,
        size_t concurrency_limit = 4096);
    // Blocking traverse never wait on a fiber future.
    bool traverse_blocking(NodeCursor, TraverseMachine &, uint64_t block_id);
    NodeCursor root() const noexcept;
    uint64_t get_latest_block_id() const;
    uint64_t get_earliest_block_id() const;
    uint64_t get_history_length() const;
    // This function moves trie from source to destination version in db
    // history. Only the RWDb can call this API for state sync purposes.
    void move_trie_version_forward(uint64_t src, uint64_t dest);

    // Load the tree of nodes in the current DB root as far as the caching
    // policy allows. RW only.
    size_t prefetch();
    // Pump any async DB operations. RO only.
    size_t poll(bool blocking, size_t count = 1);

    bool is_on_disk() const;
    bool is_read_only() const;
};

// The following are not threadsafe. Please use async get from the RODb owning
// thread.

struct AsyncContext
{
    using inflight_root_t = unordered_dense_map<
        uint64_t, std::vector<std::function<void(std::shared_ptr<Node>)>>>;
    using TrieRootCache = static_lru_cache<
        chunk_offset_t, std::shared_ptr<Node>, chunk_offset_t_hasher>;

    UpdateAux<> &aux;
    TrieRootCache root_cache;
    inflight_root_t inflight_roots;
    inflight_node_t inflight_nodes;

    AsyncContext(Db &db, size_t lru_size = 64);
    ~AsyncContext() noexcept = default;
};

using AsyncContextUniquePtr = std::unique_ptr<AsyncContext>;
AsyncContextUniquePtr async_context_create(Db &db);

namespace detail
{
    template <class T>
    struct DbGetSender
    {
        using result_type = async::result<T>;

        AsyncContext &context;

        enum op_t : uint8_t
        {
            op_get1,
            op_get_data1,
            op_get2,
            op_get_data2
        } op_type;

        std::shared_ptr<Node> root;
        NodeCursor cur;
        Nibbles const nv;
        uint64_t const block_id;
        uint8_t const cached_levels;

        using find_bytes_result_type = std::pair<byte_string, DbError>;

        find_result_type res_root;
        find_bytes_result_type res_bytes;

        constexpr DbGetSender(
            AsyncContext &context_, op_t const op_type_, NibblesView const n,
            uint64_t const block_id_, uint8_t const cached_levels_)
            : context(context_)
            , op_type(op_type_)
            , nv(n)
            , block_id(block_id_)
            , cached_levels(cached_levels_)
        {
        }

        constexpr DbGetSender(
            AsyncContext &context_, op_t const op_type_, NodeCursor const cur_,
            NibblesView const n, uint64_t const block_id_,
            uint8_t const cached_levels_)
            : context(context_)
            , op_type(op_type_)
            , cur(cur_)
            , nv(n)
            , block_id(block_id_)
            , cached_levels(cached_levels_)
        {
        }

        async::result<void>
        operator()(async::erased_connected_operation *io_state) noexcept;

        result_type completed(
            async::erased_connected_operation *,
            async::result<void> res) noexcept;
    };

}

inline detail::DbGetSender<byte_string> make_get_sender(
    AsyncContext *context, NibblesView const nv, uint64_t const block_id,
    uint8_t const cached_levels = 5)
{
    MONAD_ASSERT(context);
    return {
        *context,
        detail::DbGetSender<byte_string>::op_t::op_get1,
        nv,
        block_id,
        cached_levels};
}

inline detail::DbGetSender<byte_string> make_get_data_sender(
    AsyncContext *context, NibblesView const nv, uint64_t const block_id,
    uint8_t const cached_levels = 5)
{
    MONAD_ASSERT(context);
    return {
        *context,
        detail::DbGetSender<byte_string>::op_t::op_get_data1,
        nv,
        block_id,
        cached_levels};
}

MONAD_MPT_NAMESPACE_END
