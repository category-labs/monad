#pragma once

#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/result.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

MONAD_MPT_NAMESPACE_BEGIN

struct OnDiskDbConfig;
struct ReadOnlyOnDiskDbConfig;
struct StateMachine;
struct TraverseMachine;

class Db
{
private:
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
    Result<byte_string_view> get(NibblesView, uint64_t block_id = 0) const;
    Result<byte_string_view> get_data(NibblesView, uint64_t block_id = 0) const;
    Result<NodeCursor> get(NodeCursor, NibblesView) const;
    Result<byte_string_view> get_data(NodeCursor, NibblesView) const;

    void upsert(
        UpdateList, uint64_t block_id = 0, bool enable_compaction = true,
        bool can_write_to_fast = true);
    // It is always called from the main thread and should never wait on a
    // fiber future.
    void traverse(NibblesView prefix, TraverseMachine &, uint64_t block_id = 0);
    NodeCursor root() const noexcept;
    std::optional<uint64_t> get_latest_block_id() const;
    std::optional<uint64_t> get_earliest_block_id() const;

    // Always true if not RO. True if this DB is the latest DB (fast)
    bool is_latest() const;
    // Load the latest DB root
    void load_latest();
    // Load the tree of nodes in the current DB root as far as the caching
    // policy allows. RW only.
    size_t prefetch();
};

MONAD_MPT_NAMESPACE_END
