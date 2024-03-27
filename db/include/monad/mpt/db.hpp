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
struct StateMachine;
struct TraverseMachine;

class Db
{
private:
    struct OnDisk;

    std::unique_ptr<OnDisk> on_disk_;
    UpdateAux<> aux_;
    Node::UniquePtr root_;
    StateMachine &machine_;

public:
    // construct an in memory db
    Db(StateMachine &);
    // construct an on disk db
    Db(StateMachine &, OnDiskDbConfig const &);

    Db(Db const &) = delete;
    Db(Db &&) = delete;
    Db &operator=(Db const &) = delete;
    Db &operator=(Db &&) = delete;
    ~Db();

    // May wait on a fiber future
    Result<byte_string_view> get(NibblesView, uint64_t block_id = 0) const;
    // May wait on a fiber future
    Result<byte_string_view> get_data(NibblesView, uint64_t block_id = 0) const;
    // May wait on a fiber future
    Result<NodeCursor> get(NodeCursor, NibblesView) const;
    // May wait on a fiber future
    Result<byte_string_view> get_data(NodeCursor, NibblesView) const;
    // May wait on a fiber future
    void
    upsert(UpdateList, uint64_t block_id = 0, bool enable_compaction = true);
    // It is always called from the main thread and should never wait on a
    // fiber future.
    void traverse(NibblesView prefix, TraverseMachine &, uint64_t block_id = 0);
    NodeCursor root() const noexcept;
    std::optional<uint64_t> get_latest_block_id() const;
    std::optional<uint64_t> get_earliest_block_id() const;
};

MONAD_MPT_NAMESPACE_END
