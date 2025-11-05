// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <memory>

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/bytes.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/lru/static_lru_cache.hpp>
#include <category/core/result.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/find_request_sender.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

MONAD_MPT_NAMESPACE_BEGIN

struct OnDiskDbConfig;
struct ReadOnlyOnDiskDbConfig;
struct StateMachine;
struct TraverseMachine;
struct AsyncContext;

struct AsyncIOContext
{
    async::storage_pool pool;
    io::Ring read_ring;
    std::optional<io::Ring> write_ring;
    io::Buffers buffers;
    async::AsyncIO io;

    explicit AsyncIOContext(ReadOnlyOnDiskDbConfig const &options);
    explicit AsyncIOContext(OnDiskDbConfig const &options);
};

class RODb
{
    struct Impl;
    std::unique_ptr<Impl> impl_;

public:
    RODb(ReadOnlyOnDiskDbConfig const &);
    ~RODb();

    RODb(RODb const &) = delete;
    RODb(RODb &&) = delete;
    RODb &operator=(RODb const &) = delete;
    RODb &operator=(RODb &&) = delete;

    Result<CacheNodeCursor>
    find(CacheNodeCursor const &, NibblesView, uint64_t block_id) const;
    Result<CacheNodeCursor> find(NibblesView prefix, uint64_t block_id) const;

    uint64_t get_latest_version() const;
    uint64_t get_earliest_version() const;
    bool traverse(
        CacheNodeCursor const &, TraverseMachine &, uint64_t block_id,
        size_t concurrency_limit = 4096);
};

// RW, ROBlocking, InMemory
class Db
{
private:
    friend struct AsyncContext;

    struct Impl;
    class RWOnDisk;
    class ROOnDiskBlocking;
    class InMemory;

    std::unique_ptr<Impl> impl_;

public:
    Db(StateMachine &); // In-memory mode
    Db(StateMachine &, OnDiskDbConfig const &);
    Db(AsyncIOContext &);

    Db(Db const &) = delete;
    Db(Db &&) = delete;
    Db &operator=(Db const &) = delete;
    Db &operator=(Db &&) = delete;
    ~Db();

    // The `block_id` parameter specify the version to read from, and is also
    // used for version control validation. These calls may wait on a fiber
    // future.
    Result<NodeCursor>
    find(NodeCursor const &, NibblesView, uint64_t block_id) const;
    Result<NodeCursor> find(NibblesView prefix, uint64_t block_id) const;

    Node::SharedPtr load_root_for_version(uint64_t block_id) const;

    Node::SharedPtr copy_trie(
        Node::SharedPtr src_root, NibblesView src_prefix,
        Node::SharedPtr dest_root, NibblesView dest_prefix,
        uint64_t dest_version, bool write_root = true);

    Node::SharedPtr upsert(
        Node::SharedPtr root, UpdateList, uint64_t block_id,
        bool enable_compaction = true, bool can_write_to_fast = true,
        bool write_root = true);

    void update_finalized_version(uint64_t version);
    void update_verified_version(uint64_t version);
    void update_voted_metadata(uint64_t version, bytes32_t const &block_id);
    void update_proposed_metadata(uint64_t version, bytes32_t const &block_id);
    uint64_t get_latest_finalized_version() const;
    uint64_t get_latest_verified_version() const;
    bytes32_t get_latest_voted_block_id() const;
    uint64_t get_latest_voted_version() const;
    bytes32_t get_latest_proposed_block_id() const;
    uint64_t get_latest_proposed_version() const;

    // Traverse APIs: return value indicates if we have finished the full
    // traversal or not.
    // Parallel traversal is a single threaded out of order traverse using async
    // i/o. Note that RWDb impl waits on a fiber future, therefore any parallel
    // traverse run on RWDb should not do any blocking i/o because that will
    // block the fiber and hang. If you have to do blocking i/o during the
    // traversal on RWDb, use the `traverse_blocking` api below.
    bool traverse(
        NodeCursor const &, TraverseMachine &, uint64_t block_id,
        size_t concurrency_limit = 4096);
    // Blocking traverse never wait on a fiber future.
    bool
    traverse_blocking(NodeCursor const &, TraverseMachine &, uint64_t block_id);
    uint64_t get_latest_version() const;
    uint64_t get_earliest_version() const;
    uint64_t get_history_length() const;
    // This function moves trie from source to destination version in db
    // history. Only the RWDb can call this API for state sync purposes.
    void move_trie_version_forward(uint64_t src, uint64_t dest);

    // Load the tree of nodes in the current DB root as far as the caching
    // policy allows. RW only.
    size_t prefetch(Node::SharedPtr const &root);
    // Pump any async DB operations. RO only.
    size_t poll(bool blocking, size_t count = 1);

    bool is_on_disk() const;
    bool is_read_only() const;
};

// The following are not threadsafe. Please use async get from the RODb owning
// thread.

struct AsyncContext
{
    using inflight_root_t = ankerl::unordered_dense::segmented_map<
        uint64_t, std::vector<std::function<void(std::shared_ptr<CacheNode>)>>>;

    UpdateAux<> &aux;
    NodeCache node_cache;
    inflight_root_t inflight_roots;
    AsyncInflightNodes inflight_nodes;

    AsyncContext(Db &db, size_t node_lru_max_mem = 16ul << 20);
    ~AsyncContext() noexcept = default;
};

using AsyncContextUniquePtr = std::unique_ptr<AsyncContext>;
AsyncContextUniquePtr
async_context_create(Db &db, size_t node_lru_max_mem = 16ul << 20);

namespace detail
{
    template <return_type T>
    struct DbGetSender
    {
        using result_type = async::result<T>;

        AsyncContext &context;

        enum op_t : uint8_t
        {
            op_get1,
            op_get2,
            op_get_data1,
            op_get_data2,
            op_get_node1,
            op_get_node2
        } op_type;

        std::shared_ptr<CacheNode> root;
        CacheNodeCursor cur;
        Nibbles const nv;
        uint64_t const block_id;

        find_result_type<CacheNodeCursor> res_root;
        find_result_type<T> get_result;

        constexpr DbGetSender(
            AsyncContext &context_, op_t const op_type_, NibblesView const n,
            uint64_t const block_id_)
            : context(context_)
            , op_type(op_type_)
            , nv(n)
            , block_id(block_id_)
        {
            if constexpr (std::same_as<T, std::shared_ptr<CacheNode>>) {
                MONAD_ASSERT(op_type == op_t::op_get_node1);
            }
        }

        constexpr DbGetSender(
            AsyncContext &context_, op_t const op_type_, CacheNodeCursor cur_,
            NibblesView const n, uint64_t const block_id_)
            : context(context_)
            , op_type(op_type_)
            , cur(cur_)
            , nv(n)
            , block_id(block_id_)
        {
            if constexpr (std::same_as<T, std::shared_ptr<CacheNode>>) {
                MONAD_ASSERT(op_type == op_t::op_get_node1);
            }
        }

        async::result<void>
        operator()(async::erased_connected_operation *io_state) noexcept;

        result_type completed(
            async::erased_connected_operation *,
            async::result<void> res) noexcept;
    };
}

inline detail::TraverseSender make_traverse_sender(
    AsyncContext *const context, Node::SharedPtr traverse_root,
    std::unique_ptr<TraverseMachine> machine, uint64_t const block_id,
    size_t const concurrency_limit = 4096)
{
    MONAD_ASSERT(context);
    return {
        context->aux,
        std::move(traverse_root),
        std::move(machine),
        block_id,
        concurrency_limit};
}

inline detail::DbGetSender<byte_string> make_get_sender(
    AsyncContext *const context, NibblesView const nv, uint64_t const block_id)
{
    MONAD_ASSERT(context);
    return {
        *context,
        detail::DbGetSender<byte_string>::op_t::op_get1,
        nv,
        block_id};
}

inline detail::DbGetSender<byte_string> make_get_data_sender(
    AsyncContext *const context, NibblesView const nv, uint64_t const block_id)
{
    MONAD_ASSERT(context);
    return {
        *context,
        detail::DbGetSender<byte_string>::op_t::op_get_data1,
        nv,
        block_id};
}

inline detail::DbGetSender<std::shared_ptr<CacheNode>> make_get_node_sender(
    AsyncContext *const context, NibblesView const nv, uint64_t const block_id)
{
    MONAD_ASSERT(context);
    return {
        *context,
        detail::DbGetSender<std::shared_ptr<CacheNode>>::op_t::op_get_node1,
        nv,
        block_id};
}

MONAD_MPT_NAMESPACE_END
