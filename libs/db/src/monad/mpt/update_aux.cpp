#include <monad/async/config.hpp>
#include <monad/async/detail/start_lifetime_as_polyfill.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/detail/unsigned_20.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <stdexcept>
#include <thread>
#include <utility>
#include <vector>

#include <sys/mman.h>
#include <unistd.h>

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

// Define to avoid randomisation of free list chunks on pool creation
// This can be useful to discover bugs in code which assume chunks are
// consecutive
// #define MONAD_MPT_INITIALIZE_POOL_WITH_CONSECUTIVE_CHUNKS 1

virtual_chunk_offset_t
UpdateAuxImpl::physical_to_virtual(chunk_offset_t offset) const noexcept
{
    MONAD_ASSERT(offset.id < io->chunk_count());
    auto const *ci = db_metadata_[0]->at(offset.id);
    // should never invoke a translation for offset in free list
    MONAD_DEBUG_ASSERT(ci->in_fast_list || ci->in_slow_list);
    return {
        uint32_t(ci->insertion_count()),
        offset.offset,
        ci->in_fast_list,
        offset.spare & virtual_chunk_offset_t::max_spare};
}

std::pair<UpdateAuxImpl::chunk_list, detail::unsigned_20>
UpdateAuxImpl::chunk_list_and_age(uint32_t idx) const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const *ci = db_metadata_[0]->at(idx);
    std::pair<chunk_list, detail::unsigned_20> ret(
        chunk_list::free, ci->insertion_count());
    if (ci->in_fast_list) {
        ret.first = chunk_list::fast;
        ret.second -= db_metadata_[0]->fast_list_begin()->insertion_count();
    }
    else if (ci->in_slow_list) {
        ret.first = chunk_list::slow;
        ret.second -= db_metadata_[0]->slow_list_begin()->insertion_count();
    }
    else {
        ret.second -= db_metadata_[0]->free_list_begin()->insertion_count();
    }
    return ret;
}

void UpdateAuxImpl::append(chunk_list list, uint32_t idx) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        switch (list) {
        case chunk_list::free:
            m->append_(m->free_list, m->at_(idx));
            break;
        case chunk_list::fast:
            m->append_(m->fast_list, m->at_(idx));
            break;
        case chunk_list::slow:
            m->append_(m->slow_list, m->at_(idx));
            break;
        }
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
    if (list == chunk_list::free) {
        auto chunk = io->storage_pool().chunk(storage_pool::seq, idx);
        auto capacity = chunk->capacity();
        MONAD_DEBUG_ASSERT(chunk->size() == 0);
        db_metadata_[0]->free_capacity_add_(capacity);
        db_metadata_[1]->free_capacity_add_(capacity);
    }
}

void UpdateAuxImpl::remove(uint32_t idx) noexcept
{
    MONAD_ASSERT(is_on_disk());
    bool const is_free_list =
        (!db_metadata_[0]->at_(idx)->in_fast_list &&
         !db_metadata_[0]->at_(idx)->in_slow_list);
    auto do_ = [&](detail::db_metadata *m) { m->remove_(m->at_(idx)); };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
    if (is_free_list) {
        auto chunk = io->storage_pool().chunk(storage_pool::seq, idx);
        auto capacity = chunk->capacity();
        MONAD_DEBUG_ASSERT(chunk->size() == 0);
        db_metadata_[0]->free_capacity_sub_(capacity);
        db_metadata_[1]->free_capacity_sub_(capacity);
    }
}

void UpdateAuxImpl::advance_db_offsets_to(
    chunk_offset_t const fast_offset, chunk_offset_t const slow_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    // To detect bugs in replacing fast/slow node writer to the wrong chunk
    // list
    MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
    MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);
    auto do_ = [&](detail::db_metadata *m) {
        m->advance_db_offsets_to(detail::db_metadata::db_offsets_info_t{
            fast_offset,
            slow_offset,
            this->compact_offset_fast,
            this->compact_offset_slow,
            this->compact_offset_range_fast_,
            this->compact_offset_range_slow_});
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::append_root_offset(
    chunk_offset_t const root_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->append_root_offset(root_offset);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::update_root_offset(
    size_t const i, chunk_offset_t const root_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->update_root_offset(i, root_offset);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::fast_forward_next_version(uint64_t const version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->fast_forward_next_version(version);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::update_slow_fast_ratio_metadata() noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const ratio = (float)num_chunks(chunk_list::slow) /
                       (float)num_chunks(chunk_list::fast);
    auto do_ = [&](detail::db_metadata *m) {
        m->update_slow_fast_ratio_(ratio);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::rewind_to_match_offsets()
{
    MONAD_ASSERT(is_on_disk());
    // Free all chunks after fast_offset.id
    auto const fast_offset = db_metadata()->db_offsets.start_of_wip_offset_fast;
    MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
    auto const slow_offset = db_metadata()->db_offsets.start_of_wip_offset_slow;
    MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);

    auto const *ci = db_metadata_[0]->at(fast_offset.id);
    while (ci != db_metadata_[0]->fast_list_end()) {
        auto const idx = db_metadata_[0]->fast_list.end;
        remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx)->destroy_contents();
        append(chunk_list::free, idx);
    }
    auto fast_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, fast_offset.id);
    MONAD_ASSERT(fast_offset_chunk->try_trim_contents(fast_offset.offset));

    // Same for slow list
    auto const *slow_ci = db_metadata_[0]->at(slow_offset.id);
    while (slow_ci != db_metadata_[0]->slow_list_end()) {
        auto const idx = db_metadata_[0]->slow_list.end;
        remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx)->destroy_contents();
        append(chunk_list::free, idx);
    }
    auto slow_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, slow_offset.id);
    MONAD_ASSERT(slow_offset_chunk->try_trim_contents(slow_offset.offset));

    // Reset node_writers offset to the same offsets in db_metadata
    reset_node_writers();
}

UpdateAuxImpl::~UpdateAuxImpl()
{
    if (io != nullptr) {
        unset_io();
    }
}

#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
void UpdateAuxImpl::set_io(AsyncIO *io_)
{
    io = io_;
    auto const chunk_count = io->chunk_count();
    MONAD_ASSERT(chunk_count >= 3);
    auto const map_size =
        sizeof(detail::db_metadata) +
        chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    auto cnv_chunk = io->storage_pool().activate_chunk(storage_pool::cnv, 0);
    auto fdr = cnv_chunk->read_fd();
    auto fdw = cnv_chunk->write_fd(0);
    /* If writable, can map maps writable. If read only but allowing
    dirty, maps are made copy-on-write so writes go into RAM and don't
    affect the original. This lets us heal any metadata and make forward
    progress.
    */
    bool const can_write_to_map =
        (!io->storage_pool().is_read_only() ||
         io->storage_pool().is_read_only_allow_dirty());
    db_metadata_[0] = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        map_size,
        can_write_to_map ? (PROT_READ | PROT_WRITE) : (PROT_READ),
        io->storage_pool().is_read_only_allow_dirty() ? MAP_PRIVATE
                                                      : MAP_SHARED,
        fdw.first,
        off_t(fdr.second)));
    MONAD_ASSERT(db_metadata_[0] != MAP_FAILED);
    db_metadata_[1] = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        map_size,
        can_write_to_map ? (PROT_READ | PROT_WRITE) : (PROT_READ),
        io->storage_pool().is_read_only_allow_dirty() ? MAP_PRIVATE
                                                      : MAP_SHARED,
        fdw.first,
        off_t(fdr.second + cnv_chunk->capacity() / 2)));
    MONAD_ASSERT(db_metadata_[1] != MAP_FAILED);
    /* If on a storage which ignores TRIM, and the user just truncated
    an existing triedb, all the magics will be valid but the pool has
    been reset. Solve this by detecting when a pool has just been truncated
    and ensure all triedb structures are also reset.
    */
    if (io_->storage_pool().is_newly_truncated()) {
        memset(db_metadata_[0]->magic, 0, sizeof(db_metadata_[0]->magic));
        memset(db_metadata_[1]->magic, 0, sizeof(db_metadata_[1]->magic));
    }
    /* If the front copy vanished for some reason ... this can happen
    if something or someone zaps the front bytes of the partition.
    */
    if (0 != memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (0 == memcmp(
                     db_metadata_[1]->magic,
                     detail::db_metadata::MAGIC,
                     detail::db_metadata::MAGIC_STRING_LEN)) {
            if (can_write_to_map) {
                // Overwrite the front copy with the backup copy
                db_copy(db_metadata_[0], db_metadata_[1], map_size);
            }
            else {
                // We don't have writable maps, so can't forward progress
                throw std::runtime_error("First copy of metadata corrupted, "
                                         "but not opened for healing");
            }
        }
    }
    // Replace any dirty copy with the non-dirty copy
    if (0 == memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN) &&
        0 == memcmp(
                 db_metadata_[1]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (can_write_to_map) {
            // Replace the dirty copy with the non-dirty copy
            if (db_metadata_[0]->is_dirty().load(std::memory_order_acquire)) {
                db_copy(db_metadata_[0], db_metadata_[1], map_size);
            }
            else if (db_metadata_[1]->is_dirty().load(
                         std::memory_order_acquire)) {
                db_copy(db_metadata_[1], db_metadata_[0], map_size);
            }
        }
        else {
            if (db_metadata_[0]->is_dirty().load(std::memory_order_acquire) ||
                db_metadata_[1]->is_dirty().load(std::memory_order_acquire)) {
                // Wait a bit to see if they clear before complaining
                auto const begin = std::chrono::steady_clock::now();
                while (std::chrono::steady_clock::now() - begin <
                           std::chrono::seconds(1) &&
                       (db_metadata_[0]->is_dirty().load(
                            std::memory_order_acquire) ||
                        db_metadata_[1]->is_dirty().load(
                            std::memory_order_acquire))) {
                    std::this_thread::yield();
                }
                /* If after one second a dirty bit remains set, and we don't
                have writable maps, can't forward progress.
                */
                if (db_metadata_[0]->is_dirty().load(
                        std::memory_order_acquire) ||
                    db_metadata_[1]->is_dirty().load(
                        std::memory_order_acquire)) {
                    throw std::runtime_error("DB metadata was closed dirty, "
                                             "but not opened for healing");
                }
            }
        }
    }
    if (0 != memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        memset(db_metadata_[0], 0, map_size);
        MONAD_DEBUG_ASSERT((chunk_count & ~0xfffffU) == 0);
        db_metadata_[0]->chunk_info_count = chunk_count & 0xfffffU;
        memset(
            &db_metadata_[0]->free_list,
            0xff,
            sizeof(db_metadata_[0]->free_list));
        memset(
            &db_metadata_[0]->fast_list,
            0xff,
            sizeof(db_metadata_[0]->fast_list));
        memset(
            &db_metadata_[0]->slow_list,
            0xff,
            sizeof(db_metadata_[0]->slow_list));
        auto *chunk_info =
            start_lifetime_as_array<detail::db_metadata::chunk_info_t>(
                db_metadata_[0]->chunk_info, chunk_count);
        for (size_t n = 0; n < chunk_count; n++) {
            auto &ci = chunk_info[n];
            ci.prev_chunk_id = ci.next_chunk_id =
                detail::db_metadata::chunk_info_t::INVALID_CHUNK_ID;
        }
        // magics are not set yet, so memcpy is fine here
        memcpy(db_metadata_[1], db_metadata_[0], map_size);

        // Insert all chunks into the free list
        std::vector<uint32_t> chunks;
        chunks.reserve(chunk_count);
        for (uint32_t n = 0; n < chunk_count; n++) {
            auto chunk = io->storage_pool().chunk(storage_pool::seq, n);
            MONAD_DEBUG_ASSERT(chunk->zone_id().first == storage_pool::seq);
            MONAD_DEBUG_ASSERT(chunk->zone_id().second == n);
            MONAD_ASSERT(chunk->size() == 0); // chunks must actually be free
            chunks.push_back(n);
        }
#if !MONAD_MPT_INITIALIZE_POOL_WITH_CONSECUTIVE_CHUNKS
        small_prng rand;
        random_shuffle(chunks.begin(), chunks.end(), rand);
#endif
        auto append_with_insertion_count_override = [&](chunk_list list,
                                                        uint32_t id) {
            append(list, id);
            if (initial_insertion_count_on_pool_creation_ != 0) {
                auto override_insertion_count = [&](detail::db_metadata *db) {
                    auto g = db->hold_dirty();
                    auto *i = db->at_(id);
                    i->insertion_count0_ =
                        uint32_t(initial_insertion_count_on_pool_creation_) &
                        0x3ff;
                    i->insertion_count1_ =
                        uint32_t(
                            initial_insertion_count_on_pool_creation_ >> 10) &
                        0x3ff;
                };
                override_insertion_count(db_metadata_[0]);
                override_insertion_count(db_metadata_[1]);
            }
            auto *i = db_metadata_[0]->at_(id);
            MONAD_ASSERT(i->index(db_metadata_[0]) == id);
        };
        // root offset is the front of fast list
        chunk_offset_t const fast_offset(chunks.front(), 0);
        append_with_insertion_count_override(chunk_list::fast, fast_offset.id);
        // init the first slow chunk and slow_offset
        chunk_offset_t const slow_offset(chunks[1], 0);
        append_with_insertion_count_override(chunk_list::slow, slow_offset.id);
        std::span const chunks_after_second(
            chunks.data() + 2, chunks.size() - 2);
        // insert the rest of the chunks to free list
        for (uint32_t const i : chunks_after_second) {
            append(chunk_list::free, i);
            auto *i_ = db_metadata_[0]->at_(i);
            MONAD_ASSERT(i_->index(db_metadata_[0]) == i);
        }

        // Mark as done, init root offset and history versions for the new
        // database as invalid
        advance_db_offsets_to(fast_offset, slow_offset);
        db_metadata_[0]->root_offsets.reset_all(0);
        db_metadata_[1]->root_offsets.reset_all(0);

        std::atomic_signal_fence(
            std::memory_order_seq_cst); // no compiler reordering here
        memcpy(
            db_metadata_[0]->magic,
            detail::db_metadata::MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);
        memcpy(
            db_metadata_[1]->magic,
            detail::db_metadata::MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);

        if (!io->is_read_only()) {
            // Default behavior: initialize node writers to start at the
            // start of available slow and fast list respectively. Make sure
            // the initial fast/slow offset points into a block in use as a
            // sanity check
            reset_node_writers();
        }
    }
    else { // resume from an existing db and underlying storage devices
        if (!io->is_read_only()) {
            // Reset/init node writer's offsets, destroy contents after
            // fast_offset.id chunck
            rewind_to_match_offsets();
        }
    }
    // If the pool has changed since we configured the metadata, this will
    // fail
    MONAD_ASSERT(db_metadata_[0]->chunk_info_count == chunk_count);
}
#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif

void UpdateAuxImpl::unset_io()
{
    node_writer_fast.reset();
    node_writer_slow.reset();
    auto const chunk_count = io->chunk_count();
    auto const map_size =
        sizeof(detail::db_metadata) +
        chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    (void)::munmap(db_metadata_[0], map_size);
    (void)::munmap(db_metadata_[1], map_size);
    io = nullptr;
}

void UpdateAuxImpl::reset_node_writers()
{
    auto init_node_writer = [&](chunk_offset_t const node_writer_offset)
        -> node_writer_unique_ptr_type {
        auto chunk =
            io->storage_pool().chunk(storage_pool::seq, node_writer_offset.id);
        MONAD_ASSERT(chunk->size() >= node_writer_offset.offset);
        return io ? io->make_connected(
                        write_single_buffer_sender{
                            node_writer_offset,
                            std::min(
                                AsyncIO::WRITE_BUFFER_SIZE,
                                size_t(
                                    chunk->capacity() -
                                    node_writer_offset.offset))},
                        write_operation_io_receiver{})
                  : node_writer_unique_ptr_type{};
    };
    node_writer_fast =
        init_node_writer(db_metadata()->db_offsets.start_of_wip_offset_fast);
    node_writer_slow =
        init_node_writer(db_metadata()->db_offsets.start_of_wip_offset_slow);
}

/* upsert() supports both on disk and in memory db updates. User should
always use this interface to upsert updates to db. Here are what it does:
- if `compaction`, erase outdated history block if any, and update
compaction offsets;
- copy state from last version to new version if new version not yet exist;
- upsert `updates` should include everything nested under
version number;
- if it's on disk, update db_metadata min max versions.

Note that `version` on each call of upsert() is either the max version or max
version + 1. However, we do not assume that the version history is continuous
because user can move_trie_version_forward(), which can invalidate versions in
the middle of a continuous history.
*/
Node::UniquePtr UpdateAuxImpl::do_update(
    Node::UniquePtr prev_root, StateMachine &sm, UpdateList &&updates,
    uint64_t const version, bool const compaction, bool const can_write_to_fast)
{
    auto g(unique_lock());
    auto g2(set_current_upsert_tid());

    if (is_in_memory()) {
        return upsert(
            *this, version, sm, std::move(prev_root), std::move(updates));
    }
    MONAD_ASSERT(is_on_disk());
    set_can_write_to_fast(can_write_to_fast);

    auto const max_version = db_history_max_version();
    MONAD_ASSERT(
        max_version == INVALID_BLOCK_ID || version == max_version ||
        version == max_version + 1);
    // Erase the earliest valid version if it is going to be outdated after
    // upserting new version, advance compaction offsets
    auto const min_valid_version = db_history_min_valid_version();
    if (min_valid_version != INVALID_BLOCK_ID /* at least one valid version */
        && version - min_valid_version >= VERSION_HISTORY_LEN) {
        if (compaction) {
            auto root_to_erase = Node::UniquePtr{read_node_blocking(
                io->storage_pool(),
                get_root_offset_at_version(min_valid_version))};
            auto [min_offset_fast, min_offset_slow] =
                calc_min_offsets(*root_to_erase);
            if (min_offset_fast == INVALID_COMPACT_VIRTUAL_OFFSET) {
                min_offset_fast = MIN_COMPACT_VIRTUAL_OFFSET;
            }
            if (min_offset_slow == INVALID_COMPACT_VIRTUAL_OFFSET) {
                min_offset_slow = MIN_COMPACT_VIRTUAL_OFFSET;
            }
            remove_chunks_before_count_fast_ = min_offset_fast.get_count();
            remove_chunks_before_count_slow_ = min_offset_slow.get_count();
            advance_compact_offsets();
        }
        // erase min_valid_version, must happen before upsert() because that
        // offset may be overwritten thus invalidated in `upsert()`.
        update_root_offset(min_valid_version, INVALID_OFFSET);
    }

    auto root =
        upsert(*this, version, sm, std::move(prev_root), std::move(updates));
    MONAD_DEBUG_ASSERT(
        version - db_history_min_valid_version() + 1 <= VERSION_HISTORY_LEN);

    free_compacted_chunks();
    return root;
}

void UpdateAuxImpl::move_trie_version_forward(
    uint64_t const src, uint64_t const dest)
{
    MONAD_ASSERT(is_on_disk());
    // only allow moving forward
    MONAD_ASSERT(
        dest > src && dest != INVALID_BLOCK_ID &&
        dest >= db_history_max_version());
    auto g(unique_lock());
    auto g2(set_current_upsert_tid());
    auto const offset = get_latest_root_offset();
    update_root_offset(src, INVALID_OFFSET);
    fast_forward_next_version(dest);
    append_root_offset(offset);
}

void UpdateAuxImpl::advance_compact_offsets()
{
    MONAD_ASSERT(is_on_disk());
    // update disk growth speed trackers
    compact_virtual_chunk_offset_t const curr_fast_writer_offset{
        physical_to_virtual(node_writer_fast->sender().offset())};
    compact_virtual_chunk_offset_t const curr_slow_writer_offset{
        physical_to_virtual(node_writer_slow->sender().offset())};
    last_block_disk_growth_fast_ =
        last_block_end_offset_fast_ == 0
            ? MIN_COMPACT_VIRTUAL_OFFSET
            : curr_fast_writer_offset - last_block_end_offset_fast_;
    last_block_disk_growth_slow_ =
        last_block_end_offset_slow_ == 0
            ? MIN_COMPACT_VIRTUAL_OFFSET
            : curr_slow_writer_offset - last_block_end_offset_slow_;
    last_block_end_offset_fast_ = curr_fast_writer_offset;
    last_block_end_offset_slow_ = curr_slow_writer_offset;

    compact_offset_fast = db_metadata()->db_offsets.last_compact_offset_fast;
    compact_offset_slow = db_metadata()->db_offsets.last_compact_offset_slow;
    double const used_chunks_ratio =
        1 - num_chunks(chunk_list::free) / (double)io->chunk_count();
    compact_offset_range_fast_ = MIN_COMPACT_VIRTUAL_OFFSET;
    compact_offset_range_slow_ = MIN_COMPACT_VIRTUAL_OFFSET;
    // Compaction pace control based on free space left on disk
    if (used_chunks_ratio <= 0.8) {
        compact_offset_range_fast_.set_value(
            (uint32_t)std::lround(last_block_disk_growth_fast_ * 0.85));
    }
    else {
        auto slow_fast_inuse_ratio =
            (double)num_chunks(chunk_list::slow) / num_chunks(chunk_list::fast);
        if (db_metadata()->slow_fast_ratio == 0.0) {
            update_slow_fast_ratio_metadata();
        }
        if (slow_fast_inuse_ratio < db_metadata()->slow_fast_ratio) {
            // slow can continue to grow
            compact_offset_range_slow_.set_value((uint32_t)std::lround(
                (double)last_block_disk_growth_slow_ *
                ((double)slow_fast_inuse_ratio /
                 db_metadata()->slow_fast_ratio)));
            // more agressive compaction on fast chunks
            compact_offset_range_fast_.set_value(
                last_block_disk_growth_fast_ + last_block_disk_growth_slow_ -
                compact_offset_range_slow_ + 5);
        }
        else {
            // compact slow list more agressively until ratio is met
            compact_offset_range_fast_.set_value(
                (uint32_t)std::lround(last_block_disk_growth_fast_ * 0.99));
            // slow can continue to grow
            compact_offset_range_slow_.set_value(
                std::max(
                    db_metadata()->db_offsets.last_compact_offset_range_slow,
                    last_block_disk_growth_slow_) +
                2);
        }
    }
    compact_offset_fast += compact_offset_range_fast_;
    compact_offset_slow += compact_offset_range_slow_;
    compact_offset_range_fast_ =
        compact_offset_fast -
        db_metadata()->db_offsets.last_compact_offset_fast;
    compact_offset_range_slow_ =
        compact_offset_slow -
        db_metadata()->db_offsets.last_compact_offset_slow;
}

uint64_t UpdateAuxImpl::db_history_min_valid_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto &offsets = db_metadata()->root_offsets;
    auto min_version = db_history_range_lower_bound();
    for (; min_version != offsets.max_version(); ++min_version) {
        if (offsets[min_version] != INVALID_OFFSET) {
            break;
        }
    }
    return min_version;
}

uint64_t UpdateAuxImpl::db_history_range_lower_bound() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const max_version = db_history_max_version();
    if (max_version == INVALID_BLOCK_ID) {
        return INVALID_BLOCK_ID;
    }
    else {
        return (max_version >= VERSION_HISTORY_LEN - 1)
                   ? max_version - VERSION_HISTORY_LEN + 1
                   : 0;
    }
}

uint64_t UpdateAuxImpl::db_history_max_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return db_metadata()->get_max_version_in_history();
}

void UpdateAuxImpl::free_compacted_chunks()
{
    auto free_chunks_from_ci_till_count =
        [&](detail::db_metadata::chunk_info_t const *ci,
            uint32_t const count_before) {
            uint32_t idx = ci->index(db_metadata());
            uint32_t count =
                (uint32_t)db_metadata()->at(idx)->insertion_count();
            for (; count < count_before && ci != nullptr;
                 idx = ci->index(db_metadata()),
                 count = (uint32_t)db_metadata()->at(idx)->insertion_count()) {
                ci = ci->next(db_metadata()); // must be in this order
                remove(idx);
                io->storage_pool()
                    .chunk(monad::async::storage_pool::seq, idx)
                    ->destroy_contents();
                append(
                    UpdateAuxImpl::chunk_list::free,
                    idx); // append not prepend
            }
        };
    MONAD_ASSERT(
        remove_chunks_before_count_fast_ <=
        db_metadata()->fast_list_end()->insertion_count());
    MONAD_ASSERT(
        remove_chunks_before_count_slow_ <=
        db_metadata()->slow_list_end()->insertion_count());
    free_chunks_from_ci_till_count(
        db_metadata()->fast_list_begin(), remove_chunks_before_count_fast_);
    free_chunks_from_ci_till_count(
        db_metadata()->slow_list_begin(), remove_chunks_before_count_slow_);
}

uint32_t UpdateAuxImpl::num_chunks(chunk_list const list) const noexcept
{
    switch (list) {
    case chunk_list::free:
        return (uint32_t)(db_metadata_[0]->free_list_end()->insertion_count() -
                          db_metadata_[0]
                              ->free_list_begin()
                              ->insertion_count()) +
               1;
    case chunk_list::fast:
        return (uint32_t)(db_metadata_[0]->fast_list_end()->insertion_count() -
                          db_metadata_[0]
                              ->fast_list_begin()
                              ->insertion_count()) +
               1;
    case chunk_list::slow:
        return (uint32_t)(db_metadata_[0]->slow_list_end()->insertion_count() -
                          db_metadata_[0]
                              ->slow_list_begin()
                              ->insertion_count()) +
               1;
    }
    return 0;
}

void UpdateAuxImpl::print_update_stats()
{
#if MONAD_MPT_COLLECT_STATS
    printf("created/updated nodes: %u\n", stats.num_nodes_created);

    if (compact_offset_fast || compact_offset_slow) {
        printf(
            "#nodes copied fast to slow ring %u (%.4f), fast to fast %u "
            "(%.4f), slow to slow %u, total #nodes copied %u\n"
            "#nodes copied for compacting fast %u, #nodes copied for "
            "compacting slow %u\n",
            stats.nodes_copied_from_fast_to_slow,
            (double)stats.nodes_copied_from_fast_to_slow /
                (stats.nodes_copied_from_fast_to_slow +
                 stats.nodes_copied_from_fast_to_fast),
            stats.nodes_copied_from_fast_to_fast,
            (double)stats.nodes_copied_from_fast_to_fast /
                (stats.nodes_copied_from_fast_to_slow +
                 stats.nodes_copied_from_fast_to_fast),
            stats.nodes_copied_from_slow_to_slow,
            stats.nodes_copied_from_fast_to_slow +
                stats.nodes_copied_from_fast_to_fast +
                stats.nodes_copied_from_slow_to_slow,
            stats.nodes_copied_for_compacting_fast,
            stats.nodes_copied_for_compacting_slow);
        if (compact_offset_fast) {
            printf(
                "Fast: #compact reads before compaction offset %u / "
                "#total compact reads %u = %.4f\n",
                stats.nreads_before_offset[0],
                stats.nreads_before_offset[0] + stats.nreads_after_offset[0],
                (double)stats.nreads_before_offset[0] /
                    (stats.nreads_before_offset[0] +
                     stats.nreads_after_offset[0]));
            if (compact_offset_range_fast_) {
                printf(
                    "Fast: bytes read within compaction range %.2f MB / "
                    "compaction offset range %.2f MB = %.4f\n",
                    (double)stats.bytes_read_before_offset[0] / 1024 / 1024,
                    (double)compact_offset_range_fast_ / 16,
                    (double)stats.bytes_read_before_offset[0] /
                        compact_offset_range_fast_ / 1024 / 64);
            }
        }
        if (compact_offset_slow != 0) {
            printf(
                "Slow: #compact reads before compaction offset %u / "
                "#total compact reads %u = %.4f\n",
                stats.nreads_before_offset[1],
                stats.nreads_before_offset[1] + stats.nreads_after_offset[1],
                (double)stats.nreads_before_offset[1] /
                    (stats.nreads_before_offset[1] +
                     stats.nreads_after_offset[1]));
            if (compact_offset_range_slow_) {
                printf(
                    "Slow: bytes read within compaction range %.2f MB / "
                    "compaction offset range %.2f MB = %.4f\n",
                    (double)stats.bytes_read_before_offset[1] / 1024 / 1024,
                    (double)compact_offset_range_slow_ / 16,
                    (double)stats.bytes_read_before_offset[1] /
                        compact_offset_range_slow_ / 1024 / 64);
            }
        }
    }
#endif
}

void UpdateAuxImpl::reset_stats()
{
#if MONAD_MPT_COLLECT_STATS
    stats.reset();
#endif
}

void UpdateAuxImpl::collect_number_nodes_created_stats()
{
#if MONAD_MPT_COLLECT_STATS
    stats.num_nodes_created++;
#endif
}

void UpdateAuxImpl::collect_compaction_read_stats(
    chunk_offset_t const physical_node_offset, unsigned const bytes_to_read)
{
#if MONAD_MPT_COLLECT_STATS
    auto const node_offset = physical_to_virtual(physical_node_offset);
    if (compact_virtual_chunk_offset_t(node_offset) <
        (node_offset.in_fast_list() ? compact_offset_fast
                                    : compact_offset_slow)) {
        // node orig offset in fast list but compact to slow list
        stats.nreads_before_offset[!node_offset.in_fast_list()]++;
        stats.bytes_read_before_offset[!node_offset.in_fast_list()] +=
            bytes_to_read; // compaction bytes read
    }
    else {
        stats.nreads_after_offset[!node_offset.in_fast_list()]++;
        stats.bytes_read_before_offset[!node_offset.in_fast_list()] +=
            bytes_to_read;
    }
    stats.num_compaction_reads++; // count number of compaction reads
#else
    (void)physical_node_offset;
    (void)bytes_to_read;
#endif
}

void UpdateAuxImpl::collect_compacted_nodes_stats(
    compact_virtual_chunk_offset_t const subtrie_min_offset_fast,
    compact_virtual_chunk_offset_t const subtrie_min_offset_slow)
{
#if MONAD_MPT_COLLECT_STATS
    if (subtrie_min_offset_fast < compact_offset_fast) {
        stats.nodes_copied_for_compacting_fast++;
    }
    else if (subtrie_min_offset_slow < compact_offset_slow) {
        stats.nodes_copied_for_compacting_slow++;
    }
#else
    (void)subtrie_min_offset_fast;
    (void)subtrie_min_offset_slow;
#endif
}

void UpdateAuxImpl::collect_compacted_nodes_from_to_stats(
    chunk_offset_t const node_offset, bool const rewrite_to_fast)
{
#if MONAD_MPT_COLLECT_STATS
    if (node_offset != INVALID_OFFSET) {
        if (db_metadata()->at(node_offset.id)->in_fast_list) {
            if (!rewrite_to_fast) {
                stats.nodes_copied_from_fast_to_slow++;
            }
            else {
                stats.nodes_copied_from_fast_to_fast++;
            }
        }
        else {
            stats.nodes_copied_from_slow_to_slow++;
        }
    }
#else
    (void)node_offset;
    (void)rewrite_to_fast;

#endif
}

MONAD_MPT_NAMESPACE_END
