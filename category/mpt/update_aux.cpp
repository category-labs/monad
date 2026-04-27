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

#include <category/async/config.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/log.hpp>
#include <category/core/util/stopwatch.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/collected_stats.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/unsigned_20.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <functional>
#include <iterator>
#include <linux/fs.h>
#include <memory>
#include <optional>
#include <ranges>
#include <string>
#include <sys/ioctl.h>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

namespace
{
    uint32_t divide_and_round(uint32_t const dividend, uint64_t const divisor)
    {
        double const result = dividend / static_cast<double>(divisor);
        auto const result_floor = static_cast<uint32_t>(std::floor(result));
        double const fractional = result - result_floor;
        auto const r = static_cast<double>(rand()) / RAND_MAX;
        return result_floor + static_cast<uint32_t>(r <= fractional);
    }
}

// Returns a virtual offset on successful translation; returns
// INVALID_VIRTUAL_OFFSET if the input offset is invalid or the offset refers to
// a chunk in the free list.
virtual_chunk_offset_t
UpdateAux::physical_to_virtual(chunk_offset_t const offset) const noexcept
{
    if (offset == INVALID_OFFSET) {
        return INVALID_VIRTUAL_OFFSET;
    }
    MONAD_ASSERT(offset.id < io->chunk_count());
    auto const chunk_info = metadata_ctx_->main()->atomic_load_chunk_info(
        offset.id, std::memory_order_acquire);
    if (chunk_info.in_fast_list || chunk_info.in_slow_list) {
        return virtual_chunk_offset_t{
            uint32_t(chunk_info.insertion_count()),
            offset.offset,
            chunk_info.in_fast_list,
            0};
    }
    // return invalid virtual offset when translate an offset from free list
    return INVALID_VIRTUAL_OFFSET;
}

std::pair<UpdateAux::chunk_list, detail::unsigned_20>
UpdateAux::chunk_list_and_age(uint32_t const idx) const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const *ci = metadata_ctx_->main()->at(idx);
    std::pair<chunk_list, detail::unsigned_20> ret(
        chunk_list::free, ci->insertion_count());
    if (ci->in_fast_list) {
        ret.first = chunk_list::fast;
        ret.second -=
            metadata_ctx_->main()->fast_list_begin()->insertion_count();
    }
    else if (ci->in_slow_list) {
        ret.first = chunk_list::slow;
        ret.second -=
            metadata_ctx_->main()->slow_list_begin()->insertion_count();
    }
    else {
        ret.second -=
            metadata_ctx_->main()->free_list_begin()->insertion_count();
    }
    return ret;
}

int64_t
UpdateAux::calc_auto_expire_version(uint64_t const upsert_version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    if (metadata_ctx_->db_history_max_version() == INVALID_BLOCK_NUM) {
        return static_cast<int64_t>(upsert_version);
    }
    auto const min_valid_version =
        metadata_ctx_->db_history_min_valid_version();
    auto const max_version_post_upsert =
        std::max(metadata_ctx_->db_history_max_version(), upsert_version);
    uint64_t min_valid_version_post_upsert = min_valid_version;
    if (max_version_post_upsert - min_valid_version + 1 >
        metadata_ctx_->version_history_length()) {
        min_valid_version_post_upsert =
            max_version_post_upsert - metadata_ctx_->version_history_length() +
            1;
    }
    return std::min(
        metadata_ctx_->get_auto_expire_version_metadata() + 2,
        static_cast<int64_t>(min_valid_version_post_upsert));
}

void UpdateAux::rewind_to_match_offsets()
{
    MONAD_ASSERT(is_on_disk());

    auto const fast_offset =
        metadata_ctx_->main()->db_offsets.start_of_wip_offset_fast;
    MONAD_ASSERT(metadata_ctx_->main()->at(fast_offset.id)->in_fast_list);
    auto const slow_offset =
        metadata_ctx_->main()->db_offsets.start_of_wip_offset_slow;
    MONAD_ASSERT(metadata_ctx_->main()->at(slow_offset.id)->in_slow_list);

    // fast/slow list offsets should always be greater than last written root
    // offset.
    auto const ro = metadata_ctx_->root_offsets();
    auto const last_root_offset = ro[ro.max_version()];
    if (last_root_offset != INVALID_OFFSET) {
        auto const virtual_last_root_offset =
            physical_to_virtual(last_root_offset);
        MONAD_ASSERT(virtual_last_root_offset != INVALID_VIRTUAL_OFFSET);
        if (metadata_ctx_->main()->at(last_root_offset.id)->in_fast_list) {
            auto const virtual_fast_offset = physical_to_virtual(fast_offset);
            MONAD_ASSERT(virtual_fast_offset != INVALID_VIRTUAL_OFFSET);
            MONAD_ASSERT_PRINTF(
                virtual_fast_offset > virtual_last_root_offset,
                "Detected corruption. Last root offset (id=%d, count=%d, "
                "offset=%d) is ahead of fast list offset (id=%d, "
                "count=%d, offset=%d)",
                last_root_offset.id,
                virtual_last_root_offset.count,
                last_root_offset.offset,
                fast_offset.id,
                fast_offset.offset,
                virtual_fast_offset.count);
        }
        else if (metadata_ctx_->main()->at(last_root_offset.id)->in_slow_list) {
            auto const virtual_slow_offset = physical_to_virtual(slow_offset);
            MONAD_ASSERT(virtual_slow_offset != INVALID_VIRTUAL_OFFSET);
            MONAD_ASSERT_PRINTF(
                virtual_slow_offset > virtual_last_root_offset,
                "Detected corruption. Last root offset (id=%d, count=%d, "
                "offset=%d, is ahead of slow list offset (id=%d, "
                "count=%d, offset=%d)",
                last_root_offset.id,
                virtual_last_root_offset.count,
                last_root_offset.offset,
                slow_offset.id,
                virtual_slow_offset.count,
                slow_offset.offset);
        }
        else {
            MONAD_ABORT_PRINTF(
                "Detected corruption. Last root offset is in free list.");
        }
    }

    // Free all chunks after fast_offset.id
    auto const *ci = metadata_ctx_->main()->at(fast_offset.id);
    while (ci != metadata_ctx_->main()->fast_list_end()) {
        auto const idx = metadata_ctx_->main()->fast_list.end;
        metadata_ctx_->remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx).destroy_contents();
        metadata_ctx_->append(chunk_list::free, idx);
    }
    auto &fast_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, fast_offset.id);
    MONAD_ASSERT(fast_offset_chunk.try_trim_contents(fast_offset.offset));

    // Same for slow list
    auto const *slow_ci = metadata_ctx_->main()->at(slow_offset.id);
    while (slow_ci != metadata_ctx_->main()->slow_list_end()) {
        auto const idx = metadata_ctx_->main()->slow_list.end;
        metadata_ctx_->remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx).destroy_contents();
        metadata_ctx_->append(chunk_list::free, idx);
    }
    auto &slow_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, slow_offset.id);
    MONAD_ASSERT(slow_offset_chunk.try_trim_contents(slow_offset.offset));

    // Reset node_writers offset to the same offsets in db_metadata
    reset_node_writers();
}

void UpdateAux::clear_ondisk_db()
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](unsigned const which) {
        auto const g = metadata_ctx_->main_mutable(which)->hold_dirty();
        metadata_ctx_->root_offsets(which).reset_all(0);
    };
    do_(0);
    do_(1);
    metadata_ctx_->set_latest_finalized_version(INVALID_BLOCK_NUM);
    metadata_ctx_->set_latest_verified_version(INVALID_BLOCK_NUM);

    metadata_ctx_->set_latest_voted(INVALID_BLOCK_NUM, bytes32_t{});
    metadata_ctx_->set_latest_proposed(INVALID_BLOCK_NUM, bytes32_t{});
    metadata_ctx_->set_auto_expire_version_metadata(0);

    metadata_ctx_->advance_db_offsets_to(
        {metadata_ctx_->main()->fast_list.begin, 0},
        {metadata_ctx_->main()->slow_list.begin, 0});
    rewind_to_match_offsets();
    return;
}

void UpdateAux::rewind_to_version(uint64_t const version)
{
    MONAD_ASSERT(is_on_disk());
    MONAD_ASSERT(metadata_ctx_->version_is_valid_ondisk(version));
    if (version == metadata_ctx_->db_history_max_version()) {
        return;
    }
    auto do_ = [&](unsigned const which) {
        auto const g = metadata_ctx_->main_mutable(which)->hold_dirty();
        metadata_ctx_->root_offsets(which).rewind_to_version(version);
    };
    do_(0);
    do_(1);
    if (auto const latest_finalized =
            metadata_ctx_->get_latest_finalized_version();
        latest_finalized != INVALID_BLOCK_NUM && latest_finalized > version) {
        metadata_ctx_->set_latest_finalized_version(version);
    }
    metadata_ctx_->set_latest_verified_version(INVALID_BLOCK_NUM);
    metadata_ctx_->set_latest_voted(INVALID_BLOCK_NUM, bytes32_t{});
    metadata_ctx_->set_latest_proposed(INVALID_BLOCK_NUM, bytes32_t{});
    auto last_written_offset = metadata_ctx_->root_offsets()[version];
    bool const last_written_offset_is_in_fast_list =
        metadata_ctx_->main()->at(last_written_offset.id)->in_fast_list;
    unsigned const bytes_to_read =
        node_disk_pages_spare_15{last_written_offset}.to_pages()
        << DISK_PAGE_BITS;
    if (last_written_offset_is_in_fast_list) {
        // Form offset after the root node for future appends
        last_written_offset = round_down_align<DISK_PAGE_BITS>(
            last_written_offset.add_to_offset(bytes_to_read));
        if (last_written_offset.offset >= chunk_offset_t::max_offset) {
            last_written_offset.id = metadata_ctx_->main()
                                         ->at(last_written_offset.id)
                                         ->next_chunk_id;
            last_written_offset.offset = 0;
        }
        metadata_ctx_->advance_db_offsets_to(
            last_written_offset, metadata_ctx_->get_start_of_wip_slow_offset());
    }
    // Discard all chunks no longer in use, and if root is on fast list
    // replace the now partially written chunk with a fresh one able to be
    // appended immediately after
    rewind_to_match_offsets();
}

UpdateAux::~UpdateAux()
{
    if (io != nullptr) {
        node_writer_fast.reset();
        node_writer_slow.reset();
        io = nullptr;
        metadata_ctx_.reset();
    }
}

void UpdateAux::init(AsyncIO &io_, std::optional<uint64_t> const history_len)
{
    // Safe to call on an already-initialized instance: tear down first
    if (io != nullptr) {
        io = nullptr;
        node_writer_fast.reset();
        node_writer_slow.reset();
        metadata_ctx_.reset();
    }
    io = &io_;

    /* Block size validation: We keep accidentally running MPT on 4Kb min
    granularity storage, so error out on that early to save everybody time and
    hassle.

    Linux is unique amongst major OS kernels that it'll let you do 512 byte
    granularity i/o on a device with a higher granularity. Unfortunately, its
    implementation is buggy, and as we've seen in production it _nearly_ works
    but doesn't.

    Therefore just point blank refuse to run on storage which isn't truly 512
    byte addressable.
    */
    {
        auto const fdr =
            io->storage_pool().chunk(storage_pool::cnv, 0).read_fd();
        unsigned int logical_block_size = 0;
        unsigned int physical_block_size = 0;
        unsigned int minimum_io_size = 0;
        (void)ioctl(fdr.first, BLKSSZGET, &logical_block_size);
        (void)ioctl(fdr.first, BLKPBSZGET, &physical_block_size);
        (void)ioctl(fdr.first, BLKIOMIN, &minimum_io_size);
        MONAD_ASSERT_PRINTF(
            logical_block_size == 0 || logical_block_size == 512,
            "MPT requires storage to be addressable in 512 byte granularity. "
            "This storage has %u granularity.",
            logical_block_size);
        if (physical_block_size != 0 && physical_block_size != 512) {
            LOG_INFO_CFORMAT(
                "MPT storage has physical block size %u which is not 512 "
                "bytes.",
                physical_block_size);
        }
        if (minimum_io_size != 0 && minimum_io_size != 512) {
            LOG_INFO_CFORMAT(
                "MPT storage has minimum i/o size %u which is not 512 bytes.",
                minimum_io_size);
        }
    }

    metadata_ctx_ = std::make_unique<DbMetadataContext>(io_);

    if (metadata_ctx_->is_new_pool()) {
        metadata_ctx_->init_new_pool(
            history_len, initial_insertion_count_on_pool_creation_);
        if (history_len.has_value()) {
            enable_dynamic_history_length_ = false;
        }
        if (!io->is_read_only()) {
            reset_node_writers();
        }
    }
    else { // resume from an existing db and underlying storage devices
        if (!io->is_read_only()) {
            // Reset/init node writer's offsets, destroy contents after
            // fast_offset.id chunck
            rewind_to_match_offsets();
            if (history_len.has_value()) {
                // reset history length
                if (history_len < metadata_ctx_->version_history_length() &&
                    history_len <= metadata_ctx_->db_history_max_version()) {
                    // we invalidate earlier blocks that fall outside of the
                    // history window when shortening history length
                    erase_versions_up_to_and_including(
                        metadata_ctx_->db_history_max_version() - *history_len);
                }
                metadata_ctx_->update_history_length_metadata(*history_len);
                enable_dynamic_history_length_ = false;
            }
            else if (
                metadata_ctx_->version_history_length() < MIN_HISTORY_LENGTH) {
                // A db created by an older binary may have been shrunk to a
                // floor below the current MIN_HISTORY_LENGTH. Raise the stored
                // cap so subsequent restarts keep enough history to avoid a
                // forced statesync. Actual on-disk history will grow back to
                // the new floor as new blocks come in.
                metadata_ctx_->update_history_length_metadata(
                    MIN_HISTORY_LENGTH);
            }
        }
    }
    // If the pool has changed since we configured the metadata, this will
    // fail
    MONAD_ASSERT(metadata_ctx_->main()->chunk_info_count == io->chunk_count());
}

void UpdateAux::reset_node_writers()
{
    auto init_node_writer = [&](chunk_offset_t const node_writer_offset)
        -> node_writer_unique_ptr_type {
        auto const &chunk =
            io->storage_pool().chunk(storage_pool::seq, node_writer_offset.id);
        MONAD_ASSERT(chunk.size() >= node_writer_offset.offset);
        size_t const bytes_to_write = std::min(
            AsyncIO::WRITE_BUFFER_SIZE,
            size_t(chunk.capacity() - node_writer_offset.offset));
        return io ? io->make_connected(
                        write_single_buffer_sender{
                            node_writer_offset, bytes_to_write},
                        write_operation_io_receiver{bytes_to_write})
                  : node_writer_unique_ptr_type{};
    };
    node_writer_fast = init_node_writer(
        metadata_ctx_->main()->db_offsets.start_of_wip_offset_fast);
    node_writer_slow = init_node_writer(
        metadata_ctx_->main()->db_offsets.start_of_wip_offset_slow);

    last_block_end_offset_fast_ = compact_virtual_chunk_offset_t{
        physical_to_virtual(node_writer_fast->sender().offset())};
    last_block_end_offset_slow_ = compact_virtual_chunk_offset_t{
        physical_to_virtual(node_writer_slow->sender().offset())};
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
Node::SharedPtr UpdateAux::do_update(
    Node::SharedPtr prev_root, StateMachine &sm, UpdateList &&updates,
    uint64_t const version, bool const compaction, bool const can_write_to_fast,
    bool const write_root)
{

    if (is_in_memory()) {
        UpdateList root_updates;
        auto root_update =
            make_update({}, {}, false, std::move(updates), version);
        root_updates.push_front(root_update);
        return upsert(
            *this, version, sm, std::move(prev_root), std::move(root_updates));
    }
    MONAD_ASSERT(is_on_disk());
    set_can_write_to_fast(can_write_to_fast);

    if (prev_root) {
        // previous compaction offset
        compact_offsets = compact_offset_pair::deserialize(prev_root->value());
    }
    if (compaction) {
        if (enable_dynamic_history_length_) {
            // WARNING: this step may remove historical versions and free disk
            // chunks
            adjust_history_length_based_on_disk_usage();
        }
        if (!metadata_ctx_->version_is_valid_ondisk(version)) {
            // only advance compaction progress for non existent version
            advance_compact_offsets(prev_root);
        }
    }

    curr_upsert_auto_expire_version = calc_auto_expire_version(version);
    UpdateList root_updates;
    byte_string const compact_offsets_bytes = compact_offsets.serialize();
    auto root_update = make_update(
        {}, compact_offsets_bytes, false, std::move(updates), version);
    root_updates.push_front(root_update);

    Stopwatch<std::chrono::microseconds> const upsert_timer;
    auto root = upsert(
        *this,
        version,
        sm,
        std::move(prev_root),
        std::move(root_updates),
        write_root);
    metadata_ctx_->set_auto_expire_version_metadata(
        curr_upsert_auto_expire_version);

    auto const upsert_duration = upsert_timer.elapsed();
    if (compaction) {
        update_disk_growth_data();
        // log stats
        print_update_stats(version);
    }
    [[maybe_unused]] auto const curr_fast_writer_offset =
        physical_to_virtual(node_writer_fast->sender().offset());
    [[maybe_unused]] auto const curr_slow_writer_offset =
        physical_to_virtual(node_writer_slow->sender().offset());
    LOG_INFO_CFORMAT(
        "Finish upserting version %lu. Min valid version %lu. Time elapsed: "
        "%ld us. Disk usage: %.4f. Chunks: %u fast, %u slow, %u free. Writer "
        "offsets: fast={%u,%u}, slow={%u,%u}. Compaction head offset fast=%u, "
        "slow=%u",
        version,
        metadata_ctx_->db_history_min_valid_version(),
        upsert_duration.count(),
        disk_usage(),
        num_chunks(chunk_list::fast),
        num_chunks(chunk_list::slow),
        num_chunks(chunk_list::free),
        curr_fast_writer_offset.count,
        curr_fast_writer_offset.offset,
        curr_slow_writer_offset.count,
        curr_slow_writer_offset.offset,
        (uint32_t)compact_offsets.fast,
        (uint32_t)compact_offsets.slow);
    return root;
}

void UpdateAux::release_unreferenced_chunks()
{
    auto const min_valid_version =
        metadata_ctx_->db_history_min_valid_version();
    if (min_valid_version == INVALID_BLOCK_NUM) {
        return;
    }
    auto const min_valid_root = read_node_blocking(
        *this,
        metadata_ctx_->get_root_offset_at_version(min_valid_version),
        min_valid_version);
    auto const min_offsets =
        compact_offset_pair::deserialize(min_valid_root->value());
    MONAD_ASSERT(
        min_offsets.fast != INVALID_COMPACT_VIRTUAL_OFFSET &&
        min_offsets.slow != INVALID_COMPACT_VIRTUAL_OFFSET);
    chunks_to_remove_before_count_fast_ = min_offsets.fast.get_count();
    chunks_to_remove_before_count_slow_ = min_offsets.slow.get_count();
    LOG_INFO_CFORMAT(
        "Min valid version %lu compaction offset fast=%u, slow=%u. Remove "
        "chunks before count fast=%u, slow=%u",
        min_valid_version,
        (uint32_t)min_offsets.fast,
        (uint32_t)min_offsets.slow,
        chunks_to_remove_before_count_fast_,
        chunks_to_remove_before_count_slow_);
    MONAD_ASSERT(
        metadata_ctx_->main()->root_offsets.version_lower_bound_ >=
        min_valid_version);
    free_compacted_chunks();
}

void UpdateAux::erase_versions_up_to_and_including(uint64_t const version)
{
    LOG_INFO_CFORMAT("Erase versions up to and including %lu", version);
    clear_root_offsets_up_to_and_including(version);
    release_unreferenced_chunks();
}

double UpdateAux::calculate_disk_usage_if_erased_up_to_and_including(
    uint64_t const version_to_erase) const
{
    MONAD_ASSERT(is_on_disk());
    MONAD_ASSERT(metadata_ctx_->db_history_max_version() != INVALID_BLOCK_NUM);
    uint64_t min_version_post_erase = version_to_erase + 1;
    MONAD_ASSERT(
        min_version_post_erase < metadata_ctx_->db_history_max_version(),
        "Must have at least one valid version left after erase.");
    while (!metadata_ctx_->version_is_valid_ondisk(min_version_post_erase)) {
        min_version_post_erase++;
    }
    auto const min_valid_root_post_erase = read_node_blocking(
        *this,
        metadata_ctx_->get_root_offset_at_version(min_version_post_erase),
        min_version_post_erase);
    auto const min_offsets =
        compact_offset_pair::deserialize(min_valid_root_post_erase->value());
    MONAD_ASSERT(
        min_offsets.fast != INVALID_COMPACT_VIRTUAL_OFFSET &&
        min_offsets.slow != INVALID_COMPACT_VIRTUAL_OFFSET);
    auto const fast_list_max_count =
        metadata_ctx_->main()->fast_list_end()->insertion_count();
    auto const slow_list_max_count =
        metadata_ctx_->main()->slow_list_end()->insertion_count();
    MONAD_ASSERT(fast_list_max_count >= min_offsets.fast.get_count());
    MONAD_ASSERT(slow_list_max_count >= min_offsets.slow.get_count());
    auto const num_fast_chunks =
        fast_list_max_count - min_offsets.fast.get_count() + 1;
    auto const num_slow_chunks =
        slow_list_max_count - min_offsets.slow.get_count() + 1;
    return (num_fast_chunks + num_slow_chunks) / (double)io->chunk_count();
}

void UpdateAux::adjust_history_length_based_on_disk_usage()
{
    constexpr double upper_bound = 0.8;
    constexpr double lower_bound = 0.6;

    Stopwatch<std::chrono::microseconds> const timer;

    // Shorten history length when disk usage is high
    auto const max_version = metadata_ctx_->db_history_max_version();
    if (max_version == INVALID_BLOCK_NUM) {
        return;
    }
    auto const history_length_before =
        max_version - metadata_ctx_->db_history_min_valid_version() + 1;
    auto const current_disk_usage = disk_usage();
    if (current_disk_usage > upper_bound &&
        history_length_before > MIN_HISTORY_LENGTH) {
        uint64_t const lo = metadata_ctx_->db_history_min_valid_version();
        uint64_t const hi = max_version - MIN_HISTORY_LENGTH;
        MONAD_ASSERT(lo <= hi); // always true under the if condition
        uint64_t best_version_to_erase = hi;
        if (calculate_disk_usage_if_erased_up_to_and_including(hi) <
            upper_bound) {
            // Find the first version in range [lo, hi] where erasing up to it
            // brings disk usage <= upper_bound
            auto const versions = std::views::iota(lo, hi + 1);
            auto const it = std::ranges::lower_bound(
                versions,
                upper_bound,
                std::greater{},
                [this](uint64_t const version) {
                    return calculate_disk_usage_if_erased_up_to_and_including(
                        version);
                });

            if (it != versions.end()) {
                best_version_to_erase = *it;
            }
        }
        erase_versions_up_to_and_including(best_version_to_erase);
        metadata_ctx_->update_history_length_metadata(
            std::max(max_version - best_version_to_erase, MIN_HISTORY_LENGTH));
        MONAD_ASSERT(
            disk_usage() <= upper_bound ||
            metadata_ctx_->version_history_length() == MIN_HISTORY_LENGTH);
        LOG_INFO_CFORMAT(
            "Adjust db history length down from %lu to %lu. Current disk "
            "usage: %.4f, Time elapsed: %ld us",
            history_length_before,
            metadata_ctx_->version_history_length(),
            disk_usage(),
            timer.elapsed().count());
    }
    // Raise history length limit when disk usage falls low
    else if (auto const offsets = metadata_ctx_->root_offsets();
             current_disk_usage < lower_bound &&
             metadata_ctx_->version_history_length() < offsets.capacity()) {
        metadata_ctx_->update_history_length_metadata(offsets.capacity());
        LOG_INFO_CFORMAT(
            "Adjust db history length up from %lu to %lu. Time elapsed: %ld us",
            history_length_before,
            metadata_ctx_->version_history_length(),
            timer.elapsed().count());
    }
}

void UpdateAux::clear_root_offsets_up_to_and_including(uint64_t const version)
{
    for (uint64_t v = metadata_ctx_->db_history_range_lower_bound();
         v != INVALID_BLOCK_NUM && v <= version;
         v = metadata_ctx_->db_history_range_lower_bound()) {
        metadata_ctx_->update_root_offset(v, INVALID_OFFSET);
    }
}

void UpdateAux::move_trie_version_forward(
    uint64_t const src, uint64_t const dest)
{
    MONAD_ASSERT(is_on_disk());
    MONAD_ASSERT(metadata_ctx_->version_is_valid_ondisk(src));
    // only allow moving forward
    MONAD_ASSERT(
        dest > src && dest != INVALID_BLOCK_NUM &&
        dest >= metadata_ctx_->db_history_max_version());
    auto const offset = metadata_ctx_->get_root_offset_at_version(src);
    metadata_ctx_->update_root_offset(src, INVALID_OFFSET);
    // Must erase versions that will fall out of history range first
    if (dest >= metadata_ctx_->version_history_length()) {
        erase_versions_up_to_and_including(
            dest - metadata_ctx_->version_history_length());
    }
    metadata_ctx_->fast_forward_next_version(dest);
    metadata_ctx_->append_root_offset(offset);
    MONAD_ASSERT(dest == metadata_ctx_->db_history_max_version());
    MONAD_ASSERT(metadata_ctx_->version_is_valid_ondisk(dest));
    if (metadata_ctx_->get_auto_expire_version_metadata() ==
        static_cast<int64_t>(src)) {
        metadata_ctx_->set_auto_expire_version_metadata(
            static_cast<int64_t>(dest));
    }
}

void UpdateAux::update_disk_growth_data()
{
    compact_virtual_chunk_offset_t const curr_fast_writer_offset{
        physical_to_virtual(node_writer_fast->sender().offset())};
    compact_virtual_chunk_offset_t const curr_slow_writer_offset{
        physical_to_virtual(node_writer_slow->sender().offset())};
    last_block_disk_growth_fast_ = // unused for speed control for now
        curr_fast_writer_offset - last_block_end_offset_fast_;
    last_block_disk_growth_slow_ =
        curr_slow_writer_offset - last_block_end_offset_slow_;
    last_block_end_offset_fast_ = curr_fast_writer_offset;
    last_block_end_offset_slow_ = curr_slow_writer_offset;
}

void UpdateAux::advance_compact_offsets(Node::SharedPtr const prev_root)
{
    /* Note on ring based compaction:
    Fast list compaction is steady pace based on disk growth over recent blocks,
    and we assume no large sets of upsert work directly committed to fast list,
    meaning no greater than per block updates, otherwise there could be large
    amount of data compacted in one block.
    Large set of states upsert, like snapshot loading or state sync, should be
    written in slow ring. It is under the assumption that only small set of
    states are updated often, majority is not going to be updated in a while, so
    when block execution starts we don’t need to waste disk bandwidth to copy
    them from fast to slow.

    Compaction offset update algo:
    The fast ring is compacted at a steady pace based on the average disk growth
    across the history window (or the last block's growth if the oldest root is
    not on the fast list). Compaction head only advances when the uncompacted
    range exceeds min_versions_of_growth_before_compact_fast_list versions'
    worth of growth, to prevent over-compaction when the history window shrinks.
    Slow ring compaction begins when overall disk usage reaches
    `usage_limit_start_compact_slow` and slow list disk usage reaches
    `slow_usage_limit_start_compact_slow`. The slow list compaction range is
    adjusted according to the slow ring garbage collection ratio from the last
    block.
    */
    MONAD_ASSERT(is_on_disk());

    constexpr double fast_usage_limit_start_compaction = 0.1;
    constexpr unsigned fast_chunk_count_limit_start_compaction = 800;
    constexpr uint32_t max_compact_offset_range =
        512; // 32MB, each unit of compact_virtual_chunk_offset_t represents
             // 64KB
    // Only advance fast compaction when the fast list contains at least this
    // many versions' worth of average disk growth (prevents over-compaction)
    constexpr uint32_t min_versions_of_growth_before_compact_fast_list = 5000;
    // Small constant added to avg_disk_growth to ensure minimum progress
    constexpr uint32_t min_compaction_progress_buffer = 8;

    if (prev_root) {
        auto const min_offsets = calc_min_offsets(*prev_root);
        MONAD_ASSERT(
            !min_offsets.any_below(compact_offsets),
            "Detected referenced offsets below compaction boundary; potential "
            "disk corruption");
        if (min_offsets.fast != INVALID_COMPACT_VIRTUAL_OFFSET) {
            compact_offsets.fast = min_offsets.fast;
        }
        if (min_offsets.slow != INVALID_COMPACT_VIRTUAL_OFFSET) {
            compact_offsets.slow = min_offsets.slow;
        }
    }

    auto const fast_disk_usage =
        num_chunks(chunk_list::fast) / (double)io->chunk_count();
    uint64_t const max_version = metadata_ctx_->db_history_max_version();
    if ((fast_disk_usage < fast_usage_limit_start_compaction &&
         num_chunks(chunk_list::fast) <
             fast_chunk_count_limit_start_compaction) ||
        max_version == INVALID_BLOCK_NUM) {
        return;
    }

    MONAD_ASSERT(
        compact_offsets.fast != INVALID_COMPACT_VIRTUAL_OFFSET &&
        compact_offsets.slow != INVALID_COMPACT_VIRTUAL_OFFSET);
    /* The fast list compaction offset range is determined both by the
    average disk growth over historical blocks, and the fast list offset
    range of the latest version, so that fast-list usage adapts appropriately to
    changes in history length. */
    compact_offset_range_fast_ = MIN_COMPACT_VIRTUAL_OFFSET;

    uint64_t const min_version = metadata_ctx_->db_history_min_valid_version();
    MONAD_ASSERT(min_version != INVALID_BLOCK_NUM);
    compact_virtual_chunk_offset_t const curr_fast_writer_offset{
        physical_to_virtual(node_writer_fast->sender().offset())};
    // Estimate average fast-list disk growth per version. If the oldest root
    // is on the fast list, compute from the full history range. Otherwise fall
    // back to the last block's growth (e.g. roots from statesync may be on the
    // slow list).
    uint32_t avg_disk_growth_fast = last_block_disk_growth_fast_;
    auto const min_version_root_virtual_offset = physical_to_virtual(
        metadata_ctx_->get_root_offset_at_version(min_version));
    if (min_version_root_virtual_offset.in_fast_list() &&
        max_version > min_version) {
        avg_disk_growth_fast = divide_and_round(
            curr_fast_writer_offset -
                compact_virtual_chunk_offset_t{min_version_root_virtual_offset},
            max_version - min_version);
    }
    // Only advance the fast-list compaction offset if the uncompacted range
    // exceeds min_versions_of_growth_before_compact_fast_list (5000) versions'
    // worth of growth, to prevent over-compaction when the history window
    // shrinks.
    uint32_t const latest_block_fast_uncompacted_range =
        curr_fast_writer_offset - compact_offsets.fast;
    if (latest_block_fast_uncompacted_range >
        static_cast<uint64_t>(avg_disk_growth_fast) *
            min_versions_of_growth_before_compact_fast_list) {
        // Stride that would evenly spread the uncompacted range across the
        // history window, keeping fast-list disk usage steady over time.
        uint32_t const target_fast_compaction_stride = divide_and_round(
            latest_block_fast_uncompacted_range, max_version - min_version + 1);
        uint32_t to_advance = std::min(
            target_fast_compaction_stride,
            avg_disk_growth_fast + min_compaction_progress_buffer);
        to_advance =
            std::min(to_advance, max_compact_offset_range); // Cap at 32MB
        compact_offset_range_fast_.set_value(to_advance);
        compact_offsets.fast += compact_offset_range_fast_;
    }
    constexpr double usage_limit_start_compact_slow = 0.6;
    constexpr double slow_usage_limit_start_compact_slow = 0.2;
    double const slow_disk_usage =
        num_chunks(chunk_list::slow) / (double)io->chunk_count();
    double const total_disk_usage = fast_disk_usage + slow_disk_usage;
    // Do not compact slow list until slow list usage and total usage are both
    // above the thresholds
    if (total_disk_usage > usage_limit_start_compact_slow &&
        slow_disk_usage > slow_usage_limit_start_compact_slow) {
        // Compact slow ring: the offset is based on slow list garbage
        // collection ratio of the last block. We use the ratio of compacted
        // bytes to determine how aggressively to advance the compaction head.
        if (stats.compacted_bytes_in_slow != 0 &&
            compact_offset_range_slow_ != 0) {
            uint32_t const gc_efficiency = static_cast<uint32_t>(std::round(
                double(compact_offset_range_slow_ << 16) /
                stats.compacted_bytes_in_slow));
            // Cap at last block's growth + 1 to avoid advancing too fast
            uint32_t const new_range = std::min(
                static_cast<uint32_t>(last_block_disk_growth_slow_ + 1),
                gc_efficiency);
            compact_offset_range_slow_.set_value(new_range);
        }
        else {
            // No valid data, use minimum progress
            compact_offset_range_slow_.set_value(1);
        }
        compact_offsets.slow += compact_offset_range_slow_;
    }
    else {
        compact_offset_range_slow_ = MIN_COMPACT_VIRTUAL_OFFSET;
    }
}

void UpdateAux::free_compacted_chunks()
{
    auto free_chunks_from_ci_till_count =
        [&](detail::db_metadata::chunk_info_t const *ci,
            uint32_t const count_before) {
            uint32_t idx = ci->index(metadata_ctx_->main());
            uint32_t count =
                (uint32_t)metadata_ctx_->main()->at(idx)->insertion_count();
            for (; count < count_before && ci != nullptr;
                 idx = ci->index(metadata_ctx_->main()),
                 count = (uint32_t)metadata_ctx_->main()
                             ->at(idx)
                             ->insertion_count()) {
                ci = ci->next(metadata_ctx_->main()); // must be in this order
                Stopwatch<std::chrono::microseconds> const timer;
                metadata_ctx_->remove(idx);
                io->storage_pool()
                    .chunk(monad::async::storage_pool::seq, idx)
                    .destroy_contents();
                metadata_ctx_->append(
                    UpdateAux::chunk_list::free,
                    idx); // append not prepend
                // NOLINTNEXTLINE(bugprone-lambda-function-name)
                LOG_INFO_CFORMAT(
                    "Free compacted chunk id %u, time elapsed: %ld us",
                    idx,
                    timer.elapsed().count());
            }
        };
    MONAD_ASSERT(
        chunks_to_remove_before_count_fast_ <=
        metadata_ctx_->main()->fast_list_end()->insertion_count());
    MONAD_ASSERT(
        chunks_to_remove_before_count_slow_ <=
        metadata_ctx_->main()->slow_list_end()->insertion_count());
    free_chunks_from_ci_till_count(
        metadata_ctx_->main()->fast_list_begin(),
        chunks_to_remove_before_count_fast_);
    free_chunks_from_ci_till_count(
        metadata_ctx_->main()->slow_list_begin(),
        chunks_to_remove_before_count_slow_);
}

uint32_t UpdateAux::num_chunks(chunk_list const list) const noexcept
{
    switch (list) {
    case chunk_list::free:
        // Triggers when out of storage
        MONAD_ASSERT(metadata_ctx_->main()->free_list_begin() != nullptr);
        MONAD_ASSERT(metadata_ctx_->main()->free_list_end() != nullptr);

        return (uint32_t)(metadata_ctx_->main()
                              ->free_list_end()
                              ->insertion_count() -
                          metadata_ctx_->main()
                              ->free_list_begin()
                              ->insertion_count()) +
               1;
    case chunk_list::fast:
        // Triggers when out of storage
        MONAD_ASSERT(metadata_ctx_->main()->fast_list_begin() != nullptr);
        MONAD_ASSERT(metadata_ctx_->main()->fast_list_end() != nullptr);

        return (uint32_t)(metadata_ctx_->main()
                              ->fast_list_end()
                              ->insertion_count() -
                          metadata_ctx_->main()
                              ->fast_list_begin()
                              ->insertion_count()) +
               1;
    case chunk_list::slow:
        // Triggers when out of storage
        MONAD_ASSERT(metadata_ctx_->main()->slow_list_begin() != nullptr);
        MONAD_ASSERT(metadata_ctx_->main()->slow_list_end() != nullptr);

        return (uint32_t)(metadata_ctx_->main()
                              ->slow_list_end()
                              ->insertion_count() -
                          metadata_ctx_->main()
                              ->slow_list_begin()
                              ->insertion_count()) +
               1;
    }
    return 0;
}

void UpdateAux::print_update_stats(uint64_t const version)
{
#if MONAD_MPT_COLLECT_STATS
    if (stats.nodes_updated_expire > 50'000) {
        LOG_WARNING_CFORMAT(
            "The number of nodes updated for expire (%u) is excessively large",
            stats.nodes_updated_expire);
    }

    std::string buf;
    buf.reserve(16 << 10);
    std::format_to(
        std::back_inserter(buf),
        "Version {}: nodes created or updated for upsert = {}, nodes "
        "updated for expire = {}, nreads for expire = {}\n",
        version,
        stats.nodes_created_or_updated,
        stats.nodes_updated_expire,
        stats.nreads_expire);

    if (compact_offset_range_fast_) {
        std::format_to(
            std::back_inserter(buf),
            "   Fast: total growth ~ {} KB, compact range {} KB, "
            "bytes copied fast to slow {:.2f} KB, active data ratio {:.2f}%\n",
            last_block_disk_growth_fast_ << 6,
            compact_offset_range_fast_ << 6,
            stats.compacted_bytes_in_fast / 1024.0,
            100.0 * stats.compacted_bytes_in_fast /
                (compact_offset_range_fast_ << 16));
        if (compact_offset_range_slow_) {
            // slow list compaction range vs growth
            auto const total_bytes_written_to_slow =
                stats.compacted_bytes_in_fast + stats.compacted_bytes_in_slow;
            std::format_to(
                std::back_inserter(buf),
                "   Slow: total growth {:.2f} KB, compact range {} "
                "KB, bytes copied slow to slow {:.2f} KB, active data ratio "
                "{:.2f}%. other bytes copied slow to fast {:.2f} KB.\n",
                total_bytes_written_to_slow / 1024.0,
                compact_offset_range_slow_ << 6,
                stats.compacted_bytes_in_slow / 1024.0,
                100.0 * stats.compacted_bytes_in_slow /
                    (compact_offset_range_slow_ << 16),
                stats.bytes_copied_slow_to_fast_for_slow / 1024.0);
        }
        else {
            std::format_to(
                std::back_inserter(buf),
                "   Slow: no advance of compaction offset\n");
        }

        // num nodes copied:
        auto const nodes_copied_for_slow =
            stats.compacted_nodes_in_fast +
            stats.nodes_copied_fast_to_fast_for_fast;
        std::format_to(
            std::back_inserter(buf),
            "[Nodes Copied]\n"
            "   Fast: fast to slow {} ({:.2f}%), fast to fast {} ({:.2f}%)\n",
            stats.compacted_nodes_in_fast,
            nodes_copied_for_slow ? (100.0 * stats.compacted_nodes_in_fast /
                                     (nodes_copied_for_slow))
                                  : 0,
            stats.nodes_copied_fast_to_fast_for_fast,
            nodes_copied_for_slow
                ? (100.0 * stats.nodes_copied_fast_to_fast_for_fast /
                   nodes_copied_for_slow)
                : 0);
        if (compact_offsets.slow) {
            auto const nodes_copied_for_slow =
                stats.compacted_nodes_in_slow +
                stats.nodes_copied_fast_to_fast_for_slow +
                stats.nodes_copied_slow_to_fast_for_slow;
            std::format_to(
                std::back_inserter(buf),
                "   Slow: active slow to slow {} ({:.2f}%), fast to fast {} "
                "({:.2f}%), other slow to fast {} ({:.2f}%)\n",
                stats.compacted_nodes_in_slow,
                nodes_copied_for_slow ? (100.0 * stats.compacted_nodes_in_slow /
                                         nodes_copied_for_slow)
                                      : 0,
                stats.nodes_copied_fast_to_fast_for_slow,
                nodes_copied_for_slow
                    ? (100.0 * stats.nodes_copied_fast_to_fast_for_slow /
                       nodes_copied_for_slow)
                    : 0,
                stats.nodes_copied_slow_to_fast_for_slow,
                nodes_copied_for_slow
                    ? (100.0 * stats.nodes_copied_slow_to_fast_for_slow /
                       nodes_copied_for_slow)
                    : 0);
        }

        std::format_to(
            std::back_inserter(buf),
            "[Reads]\n"
            "   Fast: compact reads within compaction range {} / "
            "total compact reads {} = {:.2f}%\n"
            "   Fast: bytes read within compaction range {:.2f} KB / "
            "compaction range {} KB = {:.2f}%, bytes read out of "
            "compaction range {:.2f} KB\n",
            stats.nreads_before_compact_offset[0],
            stats.nreads_before_compact_offset[0] +
                stats.nreads_after_compact_offset[0],
            stats.nreads_before_compact_offset[0]
                ? (100.0 * stats.nreads_before_compact_offset[0] /
                   (stats.nreads_before_compact_offset[0] +
                    stats.nreads_after_compact_offset[0]))
                : 0,
            (double)stats.bytes_read_before_compact_offset[0] / 1024,
            compact_offset_range_fast_ << 6,
            stats.bytes_read_before_compact_offset[0]
                ? (100.0 * stats.bytes_read_before_compact_offset[0] /
                   compact_offset_range_fast_ / 1024 / 64)
                : 0,
            (double)stats.bytes_read_after_compact_offset[0] / 1024);
        if (compact_offset_range_slow_) {
            std::format_to(
                std::back_inserter(buf),
                "   Slow: reads within compaction range {} / "
                "total compact reads {} = {:.2f}%\n"
                "   Slow: bytes read within compaction range {:.2f} KB / "
                "compaction range {} KB = {:.2f}%, bytes read out of "
                "compaction range {:.2f} KB\n",
                stats.nreads_before_compact_offset[1],
                stats.nreads_before_compact_offset[1] +
                    stats.nreads_after_compact_offset[1],
                stats.nreads_before_compact_offset[1]
                    ? (100.0 * stats.nreads_before_compact_offset[1] /
                       (stats.nreads_before_compact_offset[1] +
                        stats.nreads_after_compact_offset[1]))
                    : 0,
                (double)stats.bytes_read_before_compact_offset[1] / 1024,
                compact_offset_range_slow_ << 6,
                stats.bytes_read_before_compact_offset[1]
                    ? (100.0 * stats.bytes_read_before_compact_offset[1] /
                       compact_offset_range_slow_ / 1024 / 64)
                    : 0,
                (double)stats.bytes_read_after_compact_offset[1] / 1024);
        }
    }
    LOG_INFO("{}", buf);
#else
    (void)version;
#endif
}

void UpdateAux::reset_stats()
{
    stats.reset();
}

void UpdateAux::collect_number_nodes_created_stats()
{
#if MONAD_MPT_COLLECT_STATS
    ++stats.nodes_created_or_updated;
#endif
}

void UpdateAux::collect_compaction_read_stats(
    chunk_offset_t const physical_node_offset, unsigned const bytes_to_read)
{
#if MONAD_MPT_COLLECT_STATS
    auto const node_offset = physical_to_virtual(physical_node_offset);
    if (compact_virtual_chunk_offset_t(node_offset) <
        (node_offset.in_fast_list() ? compact_offsets.fast
                                    : compact_offsets.slow)) {
        // node orig offset in fast list but compact to slow list
        ++stats.nreads_before_compact_offset[!node_offset.in_fast_list()];
        stats.bytes_read_before_compact_offset[!node_offset.in_fast_list()] +=
            bytes_to_read; // compaction bytes read
    }
    else {
        ++stats.nreads_after_compact_offset[!node_offset.in_fast_list()];
        stats.bytes_read_after_compact_offset[!node_offset.in_fast_list()] +=
            bytes_to_read;
    }
    ++stats.nreads_compaction; // count number of compaction reads
#else
    (void)physical_node_offset;
    (void)bytes_to_read;
#endif
}

void UpdateAux::collect_expire_stats(bool const is_read)
{
#if MONAD_MPT_COLLECT_STATS
    if (is_read) {
        ++stats.nreads_expire;
    }
    else {
        ++stats.nodes_updated_expire;
    }
#else
    (void)is_read;
#endif
}

void UpdateAux::collect_compacted_nodes_stats(
    bool const copy_node_for_fast, bool const rewrite_to_fast,
    virtual_chunk_offset_t const node_offset, uint32_t const node_disk_size)
{
#if MONAD_MPT_COLLECT_STATS
    if (copy_node_for_fast) {
        if (rewrite_to_fast) {
            ++stats.nodes_copied_fast_to_fast_for_fast;
        }
        else {
            ++stats.compacted_nodes_in_fast;
            stats.compacted_bytes_in_fast += node_disk_size;
        }
    }
    else { // copy node for slow
        if (rewrite_to_fast) {
            if (node_offset.in_fast_list()) {
                ++stats.nodes_copied_fast_to_fast_for_slow;
            }
            else {
                ++stats.nodes_copied_slow_to_fast_for_slow;
                stats.bytes_copied_slow_to_fast_for_slow += node_disk_size;
            }
        }
        else { // rewrite to slow
            MONAD_ASSERT(!node_offset.in_fast_list());
            MONAD_ASSERT(
                compact_virtual_chunk_offset_t{node_offset} <
                compact_offsets.slow);
            ++stats.compacted_nodes_in_slow;
            stats.compacted_bytes_in_slow += node_disk_size;
        }
    }
#else
    if (!copy_node_for_fast && !rewrite_to_fast) {
        MONAD_ASSERT(!node_offset.in_fast_list());
        MONAD_ASSERT(
            compact_virtual_chunk_offset_t{node_offset} < compact_offsets.slow);
        stats.compacted_bytes_in_slow += node_disk_size;
    }
    (void)copy_node_for_fast;
    (void)rewrite_to_fast;
#endif
}

MONAD_MPT_NAMESPACE_END
