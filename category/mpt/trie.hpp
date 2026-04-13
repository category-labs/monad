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

#include <category/async/config.hpp>
#include <category/core/bytes.hpp>
#include <category/core/lru/static_lru_cache.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/collected_stats.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/upward_tnode.hpp>
#include <category/mpt/util.hpp>

#include <category/async/io.hpp>
#include <category/async/io_senders.hpp>

#include <category/core/tl_tid.h>

#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/fiber/future.hpp>
#ifdef __clang__
    #pragma clang diagnostic pop
#endif

#include <ankerl/unordered_dense.h>

#include <atomic>
#include <bit>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <vector>

// temporary
#include "detail/boost_fiber_workarounds.hpp"

MONAD_MPT_NAMESPACE_BEGIN

class Node;

struct write_operation_io_receiver
{
    size_t should_be_written;

    // Node *parent{nullptr};

    explicit constexpr write_operation_io_receiver(
        size_t const should_be_written_)
        : should_be_written(should_be_written_)
    {
    }

    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
        MONAD_ASYNC_NAMESPACE::write_single_buffer_sender::result_type res)
    {
        MONAD_ASSERT(res);
        MONAD_ASSERT(res.assume_value().get().size() == should_be_written);
        res.assume_value()
            .get()
            .reset(); // release i/o buffer before initiating other work
        // TODO: when adding upsert_sender
        // if (parent->current_process_updates_sender_ != nullptr) {
        //     parent->current_process_updates_sender_
        //         ->notify_write_operation_completed_(rawstate);
        // }
    }

    void reset(size_t const should_be_written_)
    {
        should_be_written = should_be_written_;
    }
};

using node_writer_unique_ptr_type =
    MONAD_ASYNC_NAMESPACE::AsyncIO::connected_operation_unique_ptr_type<
        MONAD_ASYNC_NAMESPACE::write_single_buffer_sender,
        write_operation_io_receiver>;

using MONAD_ASYNC_NAMESPACE::receiver;

struct read_short_update_sender
    : MONAD_ASYNC_NAMESPACE::read_single_buffer_sender
{
    template <receiver Receiver>
    explicit constexpr read_short_update_sender(Receiver const &receiver)
        : read_single_buffer_sender(receiver.rd_offset, receiver.bytes_to_read)
    {
        MONAD_ASSERT(
            receiver.bytes_to_read <=
            MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE);
    }
};

class read_long_update_sender
    : public MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender
{
    MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender::buffer_type buffer_;

public:
    template <receiver Receiver>
    explicit read_long_update_sender(Receiver const &receiver)
        : MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender(
              receiver.rd_offset, {&buffer_, 1})
        , buffer_(
              (std::byte *)aligned_alloc(
                  DISK_PAGE_SIZE, receiver.bytes_to_read),
              receiver.bytes_to_read)
    {
        MONAD_ASSERT(
            receiver.bytes_to_read >
            MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE);
        MONAD_ASSERT(buffer_.data() != nullptr);
    }

    read_long_update_sender(read_long_update_sender &&o) noexcept
        : MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender(std::move(o))
        , buffer_(o.buffer_) // NOLINT(bugprone-use-after-move)
                             // the move only affects the base class
                             // read_multiple_buffer_sender
                             // and leaves `o.buffer_` untouched
    {
        this->reset(this->offset(), {&buffer_, 1});
        o.buffer_ = {}; // NOLINT(bugprone-use-after-move) (see above)
    }

    read_long_update_sender &operator=(read_long_update_sender &&o) noexcept

    {
        if (this != &o) {
            this->~read_long_update_sender();
            new (this) read_long_update_sender(std::move(o));
        }
        return *this;
    }

    ~read_long_update_sender()
    {
        if (buffer_.data() != nullptr) {
            ::free(buffer_.data());
            buffer_ = {};
        }
    }
};

chunk_offset_t async_write_node_set_spare(UpdateAux &, Node &, bool is_fast);

chunk_offset_t write_new_root_node(UpdateAux &, Node &root, uint64_t version);

node_writer_unique_ptr_type
replace_node_writer(UpdateAux &, node_writer_unique_ptr_type const &);

// \class Auxiliaries for triedb update
class UpdateAux
{
    void reset_node_writers();

    void advance_compact_offsets(Node::SharedPtr prev_root);

    void free_compacted_chunks();

    // clear root offsets of versions <= version
    void clear_root_offsets_up_to_and_including(uint64_t version);
    void release_unreferenced_chunks();

    double
    calculate_disk_usage_if_erased_up_to_and_including(uint64_t version) const;

    /* Calculate the version up to which the database will automatically expire
    entries (referred to as "auto_expire" in code names).

    Currently, the db auto-expires at most 2 blocks per upsert as a
    temporary workaround to reduce the sudden increase in auto-expiration
    workload during upserts that significantly shorten the history length.

    TODO: Develop a more efficient and scalable mechanism for auto-expiration
    throttling. The goal is to ensure stable database commit times despite
    varying block loads. */
    int64_t calc_auto_expire_version(uint64_t upsert_version) noexcept;

    void update_disk_growth_data();

    uint32_t initial_insertion_count_on_pool_creation_{0};
    bool enable_dynamic_history_length_{true};

    // Owns the mmap lifecycle for db_metadata. Contains the two copies of
    // mmap'd db_metadata pointers and root_offsets spans.
    std::unique_ptr<DbMetadataContext> metadata_ctx_;

    /******** Compaction ********/
    uint32_t chunks_to_remove_before_count_fast_{0};
    uint32_t chunks_to_remove_before_count_slow_{0};
    // speed control var
    compact_virtual_chunk_offset_t last_block_end_offset_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_end_offset_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_disk_growth_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_disk_growth_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    // compaction range
    compact_virtual_chunk_offset_t compact_offset_range_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_range_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};

    bool alternate_slow_fast_writer_{false};
    bool can_write_to_fast_{true};

public:
    // Allocate the first cnv chunk for db metadata copies
    static constexpr unsigned cnv_chunks_for_db_metadata = 1;

    int64_t curr_upsert_auto_expire_version{0};
    compact_offset_pair compact_offsets{
        MIN_COMPACT_VIRTUAL_OFFSET, MIN_COMPACT_VIRTUAL_OFFSET};

    // On disk stuff
    MONAD_ASYNC_NAMESPACE::AsyncIO *io{nullptr};
    node_writer_unique_ptr_type node_writer_fast{};
    node_writer_unique_ptr_type node_writer_slow{};

    detail::TrieUpdateCollectedStats stats;

    // in-memory
    UpdateAux() = default;

    // on-disk
    explicit UpdateAux(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io_,
        std::optional<uint64_t> const history_len = {})
    {
        init(io_, history_len);
    }

    ~UpdateAux();

    void init(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io_,
        std::optional<uint64_t> history_length = {});

    Node::SharedPtr do_update(
        Node::SharedPtr prev_root, StateMachine &, UpdateList &&,
        uint64_t version, bool compaction = false,
        bool can_write_to_fast = true, bool write_root = true);

    void adjust_history_length_based_on_disk_usage();
    void move_trie_version_forward(uint64_t src, uint64_t dest);

    // collect and print trie update stats
    void reset_stats();
    void collect_expire_stats(bool is_read);
    void collect_number_nodes_created_stats();
    void collect_compaction_read_stats(
        chunk_offset_t node_offset, unsigned bytes_to_read);
    void collect_compacted_nodes_stats(
        bool const copy_node_for_fast, bool const rewrite_to_fast,
        virtual_chunk_offset_t node_offset, uint32_t node_disk_size);

    void print_update_stats(uint64_t version);

    using chunk_list = DbMetadataContext::chunk_list;

    DbMetadataContext &metadata_ctx() noexcept
    {
        MONAD_ASSERT(metadata_ctx_ != nullptr);
        return *metadata_ctx_;
    }

    DbMetadataContext const &metadata_ctx() const noexcept
    {
        MONAD_ASSERT(metadata_ctx_ != nullptr);
        return *metadata_ctx_;
    }

    // clear all versions <= version, release unused disk space
    void erase_versions_up_to_and_including(uint64_t version);

    // translate between virtual and physical addresses chunk_offset_t
    virtual_chunk_offset_t physical_to_virtual(chunk_offset_t) const noexcept;

    // age is relative to the beginning chunk's count
    std::pair<chunk_list, detail::unsigned_20>
    chunk_list_and_age(uint32_t idx) const noexcept;

    // WARNING: These are destructive, they discard immediately any extraneous
    // data.
    void rewind_to_match_offsets();
    void rewind_to_version(uint64_t version);
    void clear_ondisk_db();

    void set_initial_insertion_count_unit_testing_only(uint32_t count)
    {
        initial_insertion_count_on_pool_creation_ = count;
    }

    // WARNING: for unit testing only
    // DO NOT invoke it outside of unit test
    void alternate_slow_fast_node_writer_unit_testing_only(bool alternate)
    {
        alternate_slow_fast_writer_ = alternate;
    }

    bool alternate_slow_fast_writer() const noexcept
    {
        return alternate_slow_fast_writer_;
    }

    bool can_write_to_fast() const noexcept
    {
        return can_write_to_fast_;
    }

    void set_can_write_to_fast(bool v) noexcept
    {
        can_write_to_fast_ = v;
    }

    constexpr bool is_in_memory() const noexcept
    {
        return io == nullptr;
    }

    constexpr bool is_on_disk() const noexcept
    {
        return io != nullptr;
    }

    double disk_usage() const
    {
        return 1.0 -
               (double)num_chunks(chunk_list::free) / (double)io->chunk_count();
    }

    uint32_t num_chunks(chunk_list const list) const noexcept;
};

// sizeof changed: db_metadata_[2] replaced by unique_ptr<DbMetadataContext>
static_assert(
    sizeof(UpdateAux) == 96 + sizeof(detail::TrieUpdateCollectedStats));
static_assert(alignof(UpdateAux) == 8);

template <receiver Receiver>
    requires(
        MONAD_ASYNC_NAMESPACE::compatible_sender_receiver<
            read_short_update_sender, Receiver> &&
        MONAD_ASYNC_NAMESPACE::compatible_sender_receiver<
            read_long_update_sender, Receiver> &&
        Receiver::lifetime_managed_internally)
void async_read(UpdateAux &aux, Receiver &&receiver)
{
    [[likely]] if (
        receiver.bytes_to_read <=
        MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE) {
        read_short_update_sender sender(receiver);
        auto iostate = aux.io->make_connected(
            std::move(sender), std::forward<Receiver>(receiver));
        iostate->initiate();
        // TEMPORARY UNTIL ALL THIS GETS BROKEN OUT: Release
        // management until i/o completes
        iostate.release();
    }
    else {
        read_long_update_sender sender(receiver);
        using connected_type = decltype(connect(
            *aux.io, std::move(sender), std::forward<Receiver>(receiver)));
        auto *iostate = new connected_type(connect(
            *aux.io, std::move(sender), std::forward<Receiver>(receiver)));
        iostate->initiate();
        // drop iostate
    }
}

// batch upsert, updates can be nested
Node::SharedPtr upsert(
    UpdateAux &, uint64_t version, StateMachine &, Node::SharedPtr old,
    UpdateList &&, bool write_root = true);

// Performs a deep copy of a subtrie from `src_root` trie at
// `src_prefix` to the `dest_root` trie at `dest_prefix`.
// Note that `src_root` may be of a different version than `dest_root`.
// Any pre-existing trie at `dest_prefix` will be overwritten.
// The in-memory effect is similar to a move operation.
Node::SharedPtr copy_trie_to_dest(
    UpdateAux &, Node::SharedPtr src_root, NibblesView src_prefix,
    Node::SharedPtr dest_root, NibblesView dest_prefix, uint64_t dest_version,
    bool write_root = true);

// load all nodes as far as caching policy would allow
size_t load_all(UpdateAux &, StateMachine &, NodeCursor const &);

//////////////////////////////////////////////////////////////////////////////
// find

enum class find_result : uint8_t
{
    unknown,
    success,
    version_no_longer_exist,
    root_node_is_null_failure,
    key_mismatch_failure,
    branch_not_exist_failure,
    key_ends_earlier_than_node_failure,
    need_to_continue_in_io_thread
};
template <class T>
using find_result_type = std::pair<T, find_result>;

using find_cursor_result_type = find_result_type<NodeCursor>;
using find_owning_cursor_result_type = find_result_type<NodeCursor>;

using inflight_map_owning_t = ankerl::unordered_dense::segmented_map<
    virtual_chunk_offset_t,
    std::vector<
        std::function<MONAD_ASYNC_NAMESPACE::result<void>(NodeCursor const &)>>,
    virtual_chunk_offset_t_hasher>;

// The request type to put to the fiber buffered channel for triedb thread
// to work on
struct fiber_find_request_t
{
    threadsafe_boost_fibers_promise<find_cursor_result_type> *promise;
    NodeCursor start{};
    NibblesView key{};
};

static_assert(sizeof(fiber_find_request_t) == 48);
static_assert(alignof(fiber_find_request_t) == 8);

class NodeCache;

//! \warning this is not threadsafe, should only be called from triedb thread
// during execution, DO NOT invoke it directly from a transaction fiber, as is
// not race free.
void find_notify_fiber_future(
    UpdateAux &, threadsafe_boost_fibers_promise<find_cursor_result_type> &,
    NodeCursor const &start, NibblesView key);

// rodb
void find_owning_notify_fiber_future(
    UpdateAux &, NodeCache &, inflight_map_owning_t &,
    threadsafe_boost_fibers_promise<find_owning_cursor_result_type> &promise,
    NodeCursor const &start, NibblesView, uint64_t version);

// rodb load root
void load_root_notify_fiber_future(
    UpdateAux &, NodeCache &, inflight_map_owning_t &,
    threadsafe_boost_fibers_promise<find_owning_cursor_result_type> &promise,
    uint64_t version);

/*! \brief blocking find node indexed by key from root, It works for both
on-disk and in-memory trie. When node along key is not yet in memory, it loads
the node through blocking read.

\warning Should only invoke it from the triedb owning thread, as no
synchronization is provided, and user code should make sure no other place is
modifying trie.
*/
find_cursor_result_type
find_blocking(UpdateAux const &, NodeCursor, NibblesView key, uint64_t version);

/* This function reads a node from the specified physical offset `node_offset`,
where the spare bits indicate the number of pages to read. It returns a valid
`Node::SharedPtr` on success, and returns `nullptr` if the specified version
becomes invalid.
*/
Node::SharedPtr read_node_blocking(
    UpdateAux const &, chunk_offset_t node_offset, uint64_t version);

//////////////////////////////////////////////////////////////////////////////
// helpers
inline constexpr unsigned num_pages(file_offset_t const offset, unsigned bytes)
{
    auto const rd_offset = round_down_align<DISK_PAGE_BITS>(offset);
    bytes += static_cast<unsigned>(offset - rd_offset);
    return (bytes + DISK_PAGE_SIZE - 1) >> DISK_PAGE_BITS;
}

inline compact_offset_pair calc_min_offsets(
    Node &node,
    virtual_chunk_offset_t node_virtual_offset = INVALID_VIRTUAL_OFFSET)
{
    compact_offset_pair ret;
    if (node_virtual_offset != INVALID_VIRTUAL_OFFSET) {
        auto &r = node_virtual_offset.in_fast_list() ? ret.fast : ret.slow;
        r = compact_virtual_chunk_offset_t{node_virtual_offset};
    }
    unsigned const n = node.number_of_children();
    auto const fast = node.child_min_offset_fast_data();
    auto const slow = node.child_min_offset_slow_data();
    for (unsigned i = 0; i < n; ++i) {
        ret.fast = std::min<compact_virtual_chunk_offset_t>(ret.fast, fast[i]);
        ret.slow = std::min<compact_virtual_chunk_offset_t>(ret.slow, slow[i]);
    }
    return ret;
}

MONAD_MPT_NAMESPACE_END
