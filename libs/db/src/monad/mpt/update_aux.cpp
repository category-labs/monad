#include <monad/async/config.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/detail/start_lifetime_as_polyfill.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/core/unordered_map.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/detail/unsigned_20.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <random>
#include <span>
#include <stdexcept>
#include <thread>
#include <utility>
#include <vector>

#include <sys/ioctl.h>
#include <sys/mman.h>
#include <unistd.h>

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

    std::pair<compact_virtual_chunk_offset_t, compact_virtual_chunk_offset_t>
    deserialize_compaction_offsets(byte_string_view const bytes)
    {
        MONAD_ASSERT(bytes.size() == 2 * sizeof(uint32_t));
        compact_virtual_chunk_offset_t fast_offset{
            INVALID_COMPACT_VIRTUAL_OFFSET};
        compact_virtual_chunk_offset_t slow_offset{
            INVALID_COMPACT_VIRTUAL_OFFSET};
        fast_offset.set_value(unaligned_load<uint32_t>(bytes.data()));
        slow_offset.set_value(
            unaligned_load<uint32_t>(bytes.data() + sizeof(uint32_t)));
        return {fast_offset, slow_offset};
    }
}

// Define to avoid randomisation of free list chunks on pool creation
// This can be useful to discover bugs in code which assume chunks are
// consecutive
// #define MONAD_MPT_INITIALIZE_POOL_WITH_RANDOM_SHUFFLED_CHUNKS 1
#define MONAD_MPT_INITIALIZE_POOL_WITH_REVERSE_ORDER_CHUNKS 1

virtual_chunk_offset_t
UpdateAuxImpl::physical_to_virtual(chunk_offset_t const offset) const noexcept
{
    MONAD_ASSERT(offset.id < io->chunk_count());
    auto const *ci = db_metadata()->at(offset.id);
    // should never invoke a translation for offset in free list
    MONAD_DEBUG_ASSERT(ci->in_fast_list || ci->in_slow_list);
    return {
        uint32_t(ci->insertion_count()),
        offset.offset,
        ci->in_fast_list,
        offset.spare & virtual_chunk_offset_t::max_spare};
}

std::pair<UpdateAuxImpl::chunk_list, detail::unsigned_20>
UpdateAuxImpl::chunk_list_and_age(uint32_t const idx) const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const *ci = db_metadata()->at(idx);
    std::pair<chunk_list, detail::unsigned_20> ret(
        chunk_list::free, ci->insertion_count());
    if (ci->in_fast_list) {
        ret.first = chunk_list::fast;
        ret.second -= db_metadata()->fast_list_begin()->insertion_count();
    }
    else if (ci->in_slow_list) {
        ret.first = chunk_list::slow;
        ret.second -= db_metadata()->slow_list_begin()->insertion_count();
    }
    else {
        ret.second -= db_metadata()->free_list_begin()->insertion_count();
    }
    return ret;
}

void UpdateAuxImpl::append(chunk_list const list, uint32_t const idx) noexcept
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
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
    if (list == chunk_list::free) {
        auto chunk = io->storage_pool().chunk(storage_pool::seq, idx);
        auto capacity = chunk->capacity();
        MONAD_DEBUG_ASSERT(chunk->size() == 0);
        db_metadata_[0].main->free_capacity_add_(capacity);
        db_metadata_[1].main->free_capacity_add_(capacity);
    }
}

void UpdateAuxImpl::remove(uint32_t const idx) noexcept
{
    MONAD_ASSERT(is_on_disk());
    bool const is_free_list =
        (!db_metadata_[0].main->at_(idx)->in_fast_list &&
         !db_metadata_[0].main->at_(idx)->in_slow_list);
    auto do_ = [&](detail::db_metadata *m) { m->remove_(m->at_(idx)); };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
    if (is_free_list) {
        auto chunk = io->storage_pool().chunk(storage_pool::seq, idx);
        auto capacity = chunk->capacity();
        MONAD_DEBUG_ASSERT(chunk->size() == 0);
        db_metadata_[0].main->free_capacity_sub_(capacity);
        db_metadata_[1].main->free_capacity_sub_(capacity);
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
        m->advance_db_offsets_to_(
            detail::db_metadata::db_offsets_info_t{fast_offset, slow_offset});
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

void UpdateAuxImpl::append_root_offset(
    chunk_offset_t const root_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        root_offsets(m == db_metadata_[1].main).push(root_offset);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

void UpdateAuxImpl::update_root_offset(
    size_t const i, chunk_offset_t const root_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        root_offsets(m == db_metadata_[1].main).assign(i, root_offset);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

void UpdateAuxImpl::fast_forward_next_version(
    uint64_t const new_version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        auto ro = root_offsets(m == db_metadata_[1].main);
        uint64_t curr_version = ro.max_version();

        if (new_version >= curr_version &&
            new_version - curr_version >= ro.capacity()) {
            ro.reset_all(new_version);
        }
        else {
            while (curr_version + 1 < new_version) {
                ro.push(INVALID_OFFSET);
                curr_version = ro.max_version();
            }
        }
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

void UpdateAuxImpl::update_history_length_metadata(
    uint64_t const history_len) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        auto const ro = root_offsets(m == db_metadata_[1].main);
        MONAD_ASSERT(history_len > 0 && history_len <= ro.capacity());
        reinterpret_cast<std::atomic_uint64_t *>(&m->history_length)
            ->store(history_len, std::memory_order_relaxed);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

uint64_t UpdateAuxImpl::get_latest_finalized_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return start_lifetime_as<std::atomic_uint64_t const>(
               &db_metadata()->latest_finalized_version)
        ->load(std::memory_order_acquire);
}

uint64_t UpdateAuxImpl::get_latest_verified_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return start_lifetime_as<std::atomic_uint64_t const>(
               &db_metadata()->latest_verified_version)
        ->load(std::memory_order_acquire);
}

uint64_t UpdateAuxImpl::get_latest_voted_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return start_lifetime_as<std::atomic_uint64_t const>(
               &db_metadata()->latest_voted_version)
        ->load(std::memory_order_acquire);
}

uint64_t UpdateAuxImpl::get_latest_voted_round() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return start_lifetime_as<std::atomic_uint64_t const>(
               &db_metadata()->latest_voted_round)
        ->load(std::memory_order_acquire);
}

void UpdateAuxImpl::set_latest_finalized_version(
    uint64_t const version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_finalized_version)
            ->store(version, std::memory_order_release);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

void UpdateAuxImpl::set_latest_verified_version(uint64_t const version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_verified_version)
            ->store(version, std::memory_order_release);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

void UpdateAuxImpl::set_latest_voted(
    uint64_t const version, uint64_t const round) noexcept
{
    MONAD_ASSERT(is_on_disk());
    for (auto const i : {0, 1}) {
        auto *const m = db_metadata_[i].main;
        auto g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_voted_version)
            ->store(version, std::memory_order_release);
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_voted_round)
            ->store(round, std::memory_order_release);
    }
}

int64_t UpdateAuxImpl::get_auto_expire_version_metadata() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return start_lifetime_as<std::atomic_int64_t const>(
               &db_metadata()->auto_expire_version)
        ->load(std::memory_order_acquire);
}

void UpdateAuxImpl::set_auto_expire_version_metadata(
    int64_t const version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        reinterpret_cast<std::atomic_int64_t *>(&m->auto_expire_version)
            ->store(version, std::memory_order_release);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
}

int64_t UpdateAuxImpl::calc_auto_expire_version() noexcept
{
    MONAD_ASSERT(is_on_disk());
    if (db_history_max_version() == INVALID_BLOCK_ID) {
        return 0;
    }
    auto const min_valid_version = db_history_min_valid_version();
    if (min_valid_version == db_history_max_version()) {
        return static_cast<int64_t>(min_valid_version);
    }
    auto const min_expire_version =
        static_cast<uint64_t>(get_auto_expire_version_metadata());
    return static_cast<int64_t>(
        min_valid_version > min_expire_version + 1 ? min_expire_version + 2
                                                   : min_valid_version);
}

void UpdateAuxImpl::rewind_to_match_offsets()
{
    MONAD_ASSERT(is_on_disk());

    auto const fast_offset = db_metadata()->db_offsets.start_of_wip_offset_fast;
    MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
    auto const slow_offset = db_metadata()->db_offsets.start_of_wip_offset_slow;
    MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);

    // fast/slow list offsets should always be greater than last written root
    // offset.
    auto const ro = root_offsets();
    auto const last_root_offset = ro[ro.max_version()];
    if (last_root_offset != INVALID_OFFSET) {
        auto const virtual_last_root_offset =
            physical_to_virtual(last_root_offset);
        if (db_metadata()->at(last_root_offset.id)->in_fast_list) {
            auto const virtual_fast_offset = physical_to_virtual(fast_offset);
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
        else if (db_metadata()->at(last_root_offset.id)->in_slow_list) {
            auto const virtual_slow_offset = physical_to_virtual(slow_offset);
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
    auto const *ci = db_metadata()->at(fast_offset.id);
    while (ci != db_metadata()->fast_list_end()) {
        auto const idx = db_metadata()->fast_list.end;
        remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx)->destroy_contents();
        append(chunk_list::free, idx);
    }
    auto fast_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, fast_offset.id);
    MONAD_ASSERT(fast_offset_chunk->try_trim_contents(fast_offset.offset));

    // Same for slow list
    auto const *slow_ci = db_metadata()->at(slow_offset.id);
    while (slow_ci != db_metadata()->slow_list_end()) {
        auto const idx = db_metadata()->slow_list.end;
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

void UpdateAuxImpl::clear_ondisk_db()
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        root_offsets(m == db_metadata_[1].main).reset_all(0);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
    set_latest_finalized_version(INVALID_BLOCK_ID);
    set_latest_verified_version(INVALID_BLOCK_ID);
    set_latest_voted(INVALID_BLOCK_ID, INVALID_ROUND_NUM);
    set_auto_expire_version_metadata(0);

    advance_db_offsets_to(
        {db_metadata()->fast_list.begin, 0},
        {db_metadata()->slow_list.begin, 0});
    rewind_to_match_offsets();
    return;
}

void UpdateAuxImpl::rewind_to_version(uint64_t const version)
{
    MONAD_ASSERT(is_on_disk());
    MONAD_ASSERT(version_is_valid_ondisk(version));
    if (version == db_history_max_version()) {
        return;
    }
    auto do_ = [&](detail::db_metadata *m) {
        auto g = m->hold_dirty();
        root_offsets(m == db_metadata_[1].main).rewind_to_version(version);
    };
    do_(db_metadata_[0].main);
    do_(db_metadata_[1].main);
    if (auto const latest_finalized = get_latest_finalized_version();
        latest_finalized != INVALID_BLOCK_ID && latest_finalized > version) {
        set_latest_finalized_version(version);
    }
    if (auto const latest_verified = get_latest_verified_version();
        latest_verified != INVALID_BLOCK_ID && latest_verified > version) {
        set_latest_verified_version(version);
    }
    set_latest_voted(INVALID_BLOCK_ID, INVALID_ROUND_NUM);
    auto last_written_offset = root_offsets()[version];
    bool const last_written_offset_is_in_fast_list =
        db_metadata()->at(last_written_offset.id)->in_fast_list;
    unsigned const bytes_to_read =
        node_disk_pages_spare_15{last_written_offset}.to_pages()
        << DISK_PAGE_BITS;
    if (last_written_offset_is_in_fast_list) {
        // Form offset after the root node for future appends
        last_written_offset = round_down_align<DISK_PAGE_BITS>(
            last_written_offset.add_to_offset(bytes_to_read));
        if (last_written_offset.offset >= chunk_offset_t::max_offset) {
            last_written_offset.id =
                db_metadata()->at(last_written_offset.id)->next_chunk_id;
            last_written_offset.offset = 0;
        }
        advance_db_offsets_to(
            last_written_offset, get_start_of_wip_slow_offset());
    }
    // Discard all chunks no longer in use, and if root is on fast list
    // replace the now partially written chunk with a fresh one able to be
    // appended immediately after
    rewind_to_match_offsets();
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
void UpdateAuxImpl::set_io(
    AsyncIO *io_, std::optional<uint64_t> const history_len)
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
    /* We keep accidentally running MPT on 4Kb min granularity storage, so
    error out on that early to save everybody time and hassle.

    Linux is unique amongst major OS kernels that it'll let you do 512 byte
    granularity i/o on a device with a higher granularity. Unfortunately, its
    implementation is buggy, and as we've seen in production it _nearly_ works
    but doesn't.

    Therefore just point blank refuse to run on storage which isn't truly 512
    byte addressable.
    */
    {
        unsigned int logical_block_size = 0;
        unsigned int physical_block_size = 0;
        unsigned int minimum_io_size = 0;
        // Filesystems will error on ioctl syscall, so ignore zeros. We don't
        // run production on filesystems, only the test suite and our own
        // debugging so we don't care about i/o granularity for our own dev
        // systems.
        (void)ioctl(fdr.first, BLKSSZGET, &logical_block_size);
        (void)ioctl(fdr.first, BLKPBSZGET, &physical_block_size);
        (void)ioctl(fdr.first, BLKIOMIN, &minimum_io_size);
        MONAD_ASSERT_PRINTF(
            logical_block_size == 0 || logical_block_size == 512,
            "MPT requires storage to be addressable in 512 byte granularity. "
            "This storage has %u granularity.",
            logical_block_size);
        if (physical_block_size != 0 && physical_block_size != 512) {
            std::cerr << "WARNING: MPT storage has physical block size "
                      << physical_block_size
                      << " which is not 512 bytes. This will cause performance "
                         "issues due to wasting "
                      << ((100 * (physical_block_size - 512)) /
                          physical_block_size)
                      << "% of i/o capacity!" << std::endl;
        }
        if (minimum_io_size != 0 && minimum_io_size != 512) {
            std::cerr << "WARNING: MPT storage has minimum i/o size "
                      << minimum_io_size
                      << " which is not 512 bytes. This will cause performance "
                         "issues due to wasting "
                      << ((100 * (minimum_io_size - 512)) / minimum_io_size)
                      << "% of i/o capacity!" << std::endl;
        }
    }
    /* If writable, can map maps writable. If read only but allowing
    dirty, maps are made copy-on-write so writes go into RAM and don't
    affect the original. This lets us heal any metadata and make forward
    progress.
    */
    bool const can_write_to_map =
        (!io->storage_pool().is_read_only() ||
         io->storage_pool().is_read_only_allow_dirty());
    auto &fd = can_write_to_map ? fdw : fdr;
    auto const prot = can_write_to_map ? (PROT_READ | PROT_WRITE) : (PROT_READ);
    auto const mapflags = io->storage_pool().is_read_only_allow_dirty()
                              ? MAP_PRIVATE
                              : MAP_SHARED;
    db_metadata_[0].main = start_lifetime_as<detail::db_metadata>(
        ::mmap(nullptr, map_size, prot, mapflags, fd.first, off_t(fdr.second)));
    MONAD_ASSERT(db_metadata_[0].main != MAP_FAILED);
    db_metadata_[1].main = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        map_size,
        prot,
        mapflags,
        fd.first,
        off_t(fdr.second + cnv_chunk->capacity() / 2)));
    MONAD_ASSERT(db_metadata_[1].main != MAP_FAILED);
    /* If on a storage which ignores TRIM, and the user just truncated
    an existing triedb, all the magics will be valid but the pool has
    been reset. Solve this by detecting when a pool has just been truncated
    and ensure all triedb structures are also reset.
    */
    if (io_->storage_pool().is_newly_truncated()) {
        memset(
            db_metadata_[0].main->magic,
            0,
            sizeof(db_metadata_[0].main->magic));
        memset(
            db_metadata_[1].main->magic,
            0,
            sizeof(db_metadata_[1].main->magic));
    }
    /* If the front copy vanished for some reason ... this can happen
    if something or someone zaps the front bytes of the partition.
    */
    if (0 != memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (0 == memcmp(
                     db_metadata_[1].main->magic,
                     detail::db_metadata::MAGIC,
                     detail::db_metadata::MAGIC_STRING_LEN)) {
            if (can_write_to_map) {
                // Overwrite the front copy with the backup copy
                db_copy(db_metadata_[0].main, db_metadata_[1].main, map_size);
            }
            else {
                // We don't have writable maps, so can't forward progress
                throw std::runtime_error("First copy of metadata corrupted, "
                                         "but not opened for healing");
            }
        }
    }
    constexpr unsigned magic_version_len = 3;
    constexpr unsigned magic_prefix_len =
        detail::db_metadata::MAGIC_STRING_LEN - magic_version_len;
    if (0 == memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 magic_prefix_len) &&
        memcmp(
            db_metadata_[0].main->magic + magic_prefix_len,
            detail::db_metadata::MAGIC + magic_prefix_len,
            magic_version_len)) {
        std::stringstream ss;
        ss << "DB was generated with version " << db_metadata_[0].main->magic
           << ". The current code base is on version "
           << monad::mpt::detail::db_metadata::MAGIC
           << ". Please regenerate with the new DB version.";
        throw std::runtime_error(ss.str());
    }
    // Replace any dirty copy with the non-dirty copy
    if (0 == memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN) &&
        0 == memcmp(
                 db_metadata_[1].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (can_write_to_map) {
            // Replace the dirty copy with the non-dirty copy
            if (db_metadata_[0].main->is_dirty().load(
                    std::memory_order_acquire)) {
                db_copy(db_metadata_[0].main, db_metadata_[1].main, map_size);
            }
            else if (db_metadata_[1].main->is_dirty().load(
                         std::memory_order_acquire)) {
                db_copy(db_metadata_[1].main, db_metadata_[0].main, map_size);
            }
        }
        else {
            if (db_metadata_[0].main->is_dirty().load(
                    std::memory_order_acquire) ||
                db_metadata_[1].main->is_dirty().load(
                    std::memory_order_acquire)) {
                on_read_only_init_with_dirty_bit();

                // Wait a bit to see if they clear before complaining
                bool dirty;
                auto const begin = std::chrono::steady_clock::now();
                do {
                    dirty = db_metadata_[0].main->is_dirty().load(
                                std::memory_order_acquire) ||
                            db_metadata_[1].main->is_dirty().load(
                                std::memory_order_acquire);
                    std::this_thread::yield();
                }
                while (dirty && (std::chrono::steady_clock::now() - begin <
                                 std::chrono::seconds(1)));

                /* If after one second a dirty bit remains set, and we don't
                have writable maps, can't forward progress.
                */
                if (dirty) {
                    throw std::runtime_error("DB metadata was closed dirty, "
                                             "but not opened for healing");
                }
            }
        }
    }
    auto map_root_offsets = [&] {
        if (db_metadata()->using_chunks_for_root_offsets) {
            // Map in the DB version history storage
            // Firstly reserve address space for each copy
            size_t const map_bytes_per_chunk = cnv_chunk->capacity() / 2;
            size_t const db_version_history_storage_bytes =
                db_metadata()->root_offsets.storage_.cnv_chunks_len *
                map_bytes_per_chunk;
            std::byte *reservation[2];
            reservation[0] = (std::byte *)::mmap(
                nullptr,
                db_version_history_storage_bytes,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
                -1,
                0);
            MONAD_ASSERT(reservation[0] != MAP_FAILED);
            reservation[1] = (std::byte *)::mmap(
                nullptr,
                db_version_history_storage_bytes,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
                -1,
                0);
            MONAD_ASSERT(reservation[1] != MAP_FAILED);
            // For each chunk, map the first half into the first copy and the
            // second half into the second copy
            for (size_t n = 0;
                 n < db_metadata()->root_offsets.storage_.cnv_chunks_len;
                 n++) {
                auto chunk = io->storage_pool().activate_chunk(
                    storage_pool::cnv,
                    db_metadata()
                        ->root_offsets.storage_.cnv_chunks[n]
                        .cnv_chunk_id);
                auto fdr = chunk->read_fd();
                auto fdw = chunk->write_fd(0);
                auto &fd = can_write_to_map ? fdw : fdr;
                MONAD_ASSERT(
                    MAP_FAILED != ::mmap(
                                      reservation[0] + n * map_bytes_per_chunk,
                                      map_bytes_per_chunk,
                                      prot,
                                      mapflags | MAP_FIXED,
                                      fd.first,
                                      off_t(fdr.second)));
                MONAD_ASSERT(
                    MAP_FAILED != ::mmap(
                                      reservation[1] + n * map_bytes_per_chunk,
                                      map_bytes_per_chunk,
                                      prot,
                                      mapflags | MAP_FIXED,
                                      fd.first,
                                      off_t(fdr.second + map_bytes_per_chunk)));
            }
            db_metadata_[0].root_offsets = {
                start_lifetime_as<chunk_offset_t>(
                    (chunk_offset_t *)reservation[0]),
                db_version_history_storage_bytes / sizeof(chunk_offset_t)};
            db_metadata_[1].root_offsets = {
                start_lifetime_as<chunk_offset_t>(
                    (chunk_offset_t *)reservation[1]),
                db_version_history_storage_bytes / sizeof(chunk_offset_t)};
        }
    };
    if (0 != memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (!can_write_to_map) {
            // We don't have writable maps, so can't forward progress
            throw std::runtime_error(
                "Neither copy of the DB metadata is valid, and not opened for "
                "writing so stopping now.");
        }
        for (uint32_t n = 0; n < chunk_count; n++) {
            auto chunk = io->storage_pool().chunk(storage_pool::seq, n);
            if (chunk->size() != 0) {
                throw std::runtime_error(
                    "Trying to initialise new DB but storage pool contains "
                    "existing data, stopping now to prevent data loss.");
            }
        }
        memset(db_metadata_[0].main, 0, map_size);
        MONAD_DEBUG_ASSERT((chunk_count & ~0xfffffU) == 0);
        db_metadata_[0].main->chunk_info_count = chunk_count & 0xfffffU;
        if (io->storage_pool().chunks(storage_pool::cnv) > 1) {
            auto &storage = db_metadata_[0].main->root_offsets.storage_;
            memset(&storage, 0xff, sizeof(storage));
            storage.cnv_chunks_len = 0;
            auto chunk =
                io->storage_pool().activate_chunk(storage_pool::cnv, 1);
            auto *tofill = aligned_alloc(DISK_PAGE_SIZE, chunk->capacity());
            MONAD_ASSERT(tofill != nullptr);
            auto untofill = make_scope_exit([&]() noexcept { ::free(tofill); });
            memset(tofill, 0xff, chunk->capacity());
            {
                auto fdw = chunk->write_fd(chunk->capacity());
                MONAD_ASSERT(
                    -1 != ::pwrite(
                              fdw.first,
                              tofill,
                              chunk->capacity(),
                              (off_t)fdw.second));
            }
            storage.cnv_chunks[storage.cnv_chunks_len++].cnv_chunk_id = 1;
            db_metadata_[0].main->using_chunks_for_root_offsets = true;
            db_metadata_[0].main->history_length =
                chunk->capacity() / 2 / sizeof(chunk_offset_t);
            // Gobble up all remaining cnv chunks
            for (uint32_t n = 2;
                 n < io->storage_pool().chunks(storage_pool::cnv);
                 n++) {
                auto chunk =
                    io->storage_pool().activate_chunk(storage_pool::cnv, n);
                auto fdw = chunk->write_fd(chunk->capacity());
                MONAD_ASSERT(
                    -1 != ::pwrite(
                              fdw.first,
                              tofill,
                              chunk->capacity(),
                              (off_t)fdw.second));
                storage.cnv_chunks[storage.cnv_chunks_len++].cnv_chunk_id = n;
                db_metadata_[0].main->history_length +=
                    chunk->capacity() / 2 / sizeof(chunk_offset_t);
            }
        }
        else {
            db_metadata_[0].main->history_length =
                detail::db_metadata::root_offsets_ring_t::SIZE_;
        }
        memset(
            &db_metadata_[0].main->free_list,
            0xff,
            sizeof(db_metadata_[0].main->free_list));
        memset(
            &db_metadata_[0].main->fast_list,
            0xff,
            sizeof(db_metadata_[0].main->fast_list));
        memset(
            &db_metadata_[0].main->slow_list,
            0xff,
            sizeof(db_metadata_[0].main->slow_list));
        auto *chunk_info =
            start_lifetime_as_array<detail::db_metadata::chunk_info_t>(
                db_metadata_[0].main->chunk_info, chunk_count);
        for (size_t n = 0; n < chunk_count; n++) {
            auto &ci = chunk_info[n];
            ci.prev_chunk_id = ci.next_chunk_id =
                detail::db_metadata::chunk_info_t::INVALID_CHUNK_ID;
        }
        // magics are not set yet, so memcpy is fine here
        memcpy(db_metadata_[1].main, db_metadata_[0].main, map_size);

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

#if MONAD_MPT_INITIALIZE_POOL_WITH_REVERSE_ORDER_CHUNKS
        std::reverse(chunks.begin(), chunks.end());
        LOG_INFO_CFORMAT(
            "Initialize db pool with %zu chunks in reverse order.",
            chunk_count);
#elif MONAD_MPT_INITIALIZE_POOL_WITH_RANDOM_SHUFFLED_CHUNKS
        LOG_INFO_CFORMAT(
            "Initialize db pool with %zu chunks in random order.", chunk_count);
        small_prng rand;
        random_shuffle(chunks.begin(), chunks.end(), rand);
#else
        LOG_INFO_CFORMAT(
            "Initialize db pool with %zu chunks in increasing order.",
            chunk_count);
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
                override_insertion_count(db_metadata_[0].main);
                override_insertion_count(db_metadata_[1].main);
            }
            auto *i = db_metadata_[0].main->at_(id);
            MONAD_ASSERT(i->index(db_metadata()) == id);
        };
        // root offset is the front of fast list
        chunk_offset_t const fast_offset(chunks.front(), 0);
        append_with_insertion_count_override(chunk_list::fast, fast_offset.id);
        LOG_DEBUG_CFORMAT(
            "Append one chunk to fast list, id: %d", fast_offset.id);
        // init the first slow chunk and slow_offset
        chunk_offset_t const slow_offset(chunks[1], 0);
        append_with_insertion_count_override(chunk_list::slow, slow_offset.id);
        LOG_DEBUG_CFORMAT(
            "Append one chunk to slow list, id: %d", slow_offset.id);
        std::span const chunks_after_second(
            chunks.data() + 2, chunks.size() - 2);
        // insert the rest of the chunks to free list
        for (uint32_t const i : chunks_after_second) {
            append(chunk_list::free, i);
            auto *i_ = db_metadata_[0].main->at_(i);
            MONAD_ASSERT(i_->index(db_metadata()) == i);
        }

        // Mark as done, init root offset and history versions for the new
        // database as invalid
        advance_db_offsets_to(fast_offset, slow_offset);
        if (!db_metadata_[0].main->using_chunks_for_root_offsets) {
            root_offsets(0).reset_all(0);
            root_offsets(1).reset_all(0);
        }
        set_latest_finalized_version(INVALID_BLOCK_ID);
        set_latest_verified_version(INVALID_BLOCK_ID);
        set_latest_voted(INVALID_BLOCK_ID, INVALID_ROUND_NUM);
        set_auto_expire_version_metadata(0);

        for (auto const i : {0, 1}) {
            auto *const m = db_metadata_[i].main;
            auto g = m->hold_dirty();
            memset(
                m->future_variables_unused,
                0xff,
                sizeof(m->future_variables_unused));
        }

        // Set history length
        if (history_len.has_value()) {
            update_history_length_metadata(*history_len);
            enable_dynamic_history_length_ = false;
        }

        std::atomic_signal_fence(
            std::memory_order_seq_cst); // no compiler reordering here
        memcpy(
            db_metadata_[0].main->magic,
            detail::db_metadata::MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);
        memcpy(
            db_metadata_[1].main->magic,
            detail::db_metadata::MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);

        map_root_offsets();
        if (!io->is_read_only()) {
            // Default behavior: initialize node writers to start at the
            // start of available slow and fast list respectively. Make sure
            // the initial fast/slow offset points into a block in use as a
            // sanity check
            reset_node_writers();
        }
    }
    else { // resume from an existing db and underlying storage devices
        map_root_offsets();
        if (!io->is_read_only()) {
            // Reset/init node writer's offsets, destroy contents after
            // fast_offset.id chunck
            rewind_to_match_offsets();
            if (history_len.has_value()) {
                // reset history length
                if (history_len < version_history_length() &&
                    history_len <= db_history_max_version()) {
                    // we invalidate earlier blocks that fall outside of the
                    // history window when shortening history length
                    for (auto version = db_history_min_valid_version();
                         version <= db_history_max_version() - *history_len;
                         ++version) {
                        update_root_offset(version, INVALID_OFFSET);
                    }
                }
                update_history_length_metadata(*history_len);
                enable_dynamic_history_length_ = false;
            }
        }
    }
    // If the pool has changed since we configured the metadata, this will
    // fail
    MONAD_ASSERT(db_metadata()->chunk_info_count == chunk_count);
}
#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif

void UpdateAuxImpl::unset_io()
{
    node_writer_fast.reset();
    node_writer_slow.reset();
    if (db_metadata_[0].root_offsets.data() != nullptr) {
        (void)::munmap(
            db_metadata_[0].root_offsets.data(),
            db_metadata_[0].root_offsets.size_bytes());
        db_metadata_[0].root_offsets = {};
    }
    if (db_metadata_[1].root_offsets.data() != nullptr) {
        (void)::munmap(
            db_metadata_[1].root_offsets.data(),
            db_metadata_[1].root_offsets.size_bytes());
        db_metadata_[1].root_offsets = {};
    }
    auto const chunk_count = io->chunk_count();
    auto const map_size =
        sizeof(detail::db_metadata) +
        chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    (void)::munmap(db_metadata_[0].main, map_size);
    db_metadata_[0].main = nullptr;
    (void)::munmap(db_metadata_[1].main, map_size);
    db_metadata_[1].main = nullptr;
    io = nullptr;
}

void UpdateAuxImpl::reset_node_writers()
{
    auto init_node_writer = [&](chunk_offset_t const node_writer_offset)
        -> node_writer_unique_ptr_type {
        auto chunk =
            io->storage_pool().chunk(storage_pool::seq, node_writer_offset.id);
        MONAD_ASSERT(chunk->size() >= node_writer_offset.offset);
        size_t const bytes_to_write = std::min(
            AsyncIO::WRITE_BUFFER_SIZE,
            size_t(chunk->capacity() - node_writer_offset.offset));
        return io ? io->make_connected(
                        write_single_buffer_sender{
                            node_writer_offset, bytes_to_write},
                        write_operation_io_receiver{bytes_to_write})
                  : node_writer_unique_ptr_type{};
    };
    node_writer_fast =
        init_node_writer(db_metadata()->db_offsets.start_of_wip_offset_fast);
    node_writer_slow =
        init_node_writer(db_metadata()->db_offsets.start_of_wip_offset_slow);

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
Node::UniquePtr UpdateAuxImpl::do_update(
    Node::UniquePtr prev_root, StateMachine &sm, UpdateList &&updates,
    uint64_t const version, bool const compaction, bool const can_write_to_fast,
    bool const write_root)
{
    auto g(unique_lock());
    auto g2(set_current_upsert_tid());

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

    if (compaction) {
        if (enable_dynamic_history_length_) {
            // WARNING: this step may remove historical versions and free disk
            // chunks
            adjust_history_length_based_on_disk_usage();
        }
        if (prev_root) {
            advance_compact_offsets(*prev_root, version);
        }
        else { // no compaction if trie upsert on an empty trie
            compact_offset_fast = MIN_COMPACT_VIRTUAL_OFFSET;
            compact_offset_slow = MIN_COMPACT_VIRTUAL_OFFSET;
        }
    }

    // Erase the earliest valid version if it is going to be outdated after
    // upserting new version
    if (auto const min_valid_version = db_history_min_valid_version();
        version > min_valid_version &&
        min_valid_version != INVALID_BLOCK_ID /* at least one valid version */
        && version - min_valid_version >= version_history_length()) {
        // erase min_valid_version, must happen before upsert() because that
        // offset slot in ring buffer may be overwritten thus invalidated in
        // `upsert()`.
        erase_version(min_valid_version);
    }
    curr_upsert_auto_expire_version = calc_auto_expire_version();
    UpdateList root_updates;
    byte_string const compact_offsets_bytes =
        version_is_valid_ondisk(version)
            ? byte_string{prev_root->value()}
            : serialize((uint32_t)compact_offset_fast) +
                  serialize((uint32_t)compact_offset_slow);
    auto root_update = make_update(
        {}, compact_offsets_bytes, false, std::move(updates), version);
    root_updates.push_front(root_update);

    auto upsert_begin = std::chrono::steady_clock::now();
    auto root = upsert(
        *this,
        version,
        sm,
        std::move(prev_root),
        std::move(root_updates),
        write_root);
    set_auto_expire_version_metadata(curr_upsert_auto_expire_version);

    auto const duration = std::chrono::duration_cast<std::chrono::microseconds>(
        std::chrono::steady_clock::now() - upsert_begin);
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
        "Finish upserting version %lu. Time elapsed: %ld us. Disk usage: %.4f. "
        "Chunks: %u fast, %u slow, %u free. Writer offsets: fast={%u,%u}, "
        "slow={%u,%u}.",
        version,
        duration.count(),
        disk_usage(),
        num_chunks(chunk_list::fast),
        num_chunks(chunk_list::slow),
        num_chunks(chunk_list::free),
        curr_fast_writer_offset.count,
        curr_fast_writer_offset.offset,
        curr_slow_writer_offset.count,
        curr_slow_writer_offset.offset);
    if (duration > std::chrono::microseconds(500'000)) {
        LOG_WARNING_CFORMAT(
            "Upsert version %lu takes longer than 0.5 s, time elapsed: %ld us.",
            version,
            duration.count());
    }
    return root;
}

void UpdateAuxImpl::erase_version(uint64_t const version)
{
    Node::UniquePtr root_to_erase =
        read_node_blocking(*this, get_root_offset_at_version(version), version);
    auto const [min_offset_fast, min_offset_slow] =
        deserialize_compaction_offsets(root_to_erase->value());
    MONAD_ASSERT(
        min_offset_fast != INVALID_COMPACT_VIRTUAL_OFFSET &&
        min_offset_slow != INVALID_COMPACT_VIRTUAL_OFFSET);
    chunks_to_remove_before_count_fast_ = min_offset_fast.get_count();
    chunks_to_remove_before_count_slow_ = min_offset_slow.get_count();
    // MUST NOT CHANGE ORDER
    // Remove the root from the ring buffer before recycling disk chunks
    // ensures crash recovery integrity
    update_root_offset(version, INVALID_OFFSET);
    free_compacted_chunks();
}

void UpdateAuxImpl::adjust_history_length_based_on_disk_usage()
{
    constexpr double upper_bound = 0.8;
    constexpr double lower_bound = 0.6;

    // Shorten history length when disk usage is high
    auto const max_version = db_history_max_version();
    if (max_version == INVALID_BLOCK_ID) {
        return;
    }
    auto const history_length_before =
        max_version - db_history_min_valid_version() + 1;
    auto const current_disk_usage = disk_usage();
    if (current_disk_usage > upper_bound &&
        history_length_before > MIN_HISTORY_LENGTH) {
        while (disk_usage() > upper_bound &&
               version_history_length() > MIN_HISTORY_LENGTH) {
            auto const version_to_erase = db_history_min_valid_version();
            MONAD_ASSERT(
                version_to_erase != INVALID_BLOCK_ID &&
                version_to_erase < max_version);
            erase_version(version_to_erase);
            update_history_length_metadata(
                std::max(max_version - version_to_erase, MIN_HISTORY_LENGTH));
        }
        MONAD_ASSERT(
            disk_usage() <= upper_bound ||
            version_history_length() == MIN_HISTORY_LENGTH);
        LOG_INFO_CFORMAT(
            "Adjust db history length down from %lu to %lu",
            history_length_before,
            version_history_length());
    }
    // Raise history length limit when disk usage falls low
    else if (auto const offsets = root_offsets();
             current_disk_usage < lower_bound &&
             version_history_length() < offsets.capacity()) {
        update_history_length_metadata(offsets.capacity());
        LOG_INFO_CFORMAT(
            "Adjust db history length up from %lu to %lu",
            history_length_before,
            version_history_length());
    }
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

void UpdateAuxImpl::update_disk_growth_data()
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

void UpdateAuxImpl::advance_compact_offsets(
    Node &prev_root, uint64_t const version)
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
    observed over recent blocks. We define two disk usage thresholds:
    `usage_limit_start_compact_slow` and `usage_limit`. When disk usage reaches
    `usage_limit_start_compact_slow`, slow ring compaction begins, guided by the
    slow ring garbage collection ratio from the last block. If disk usage
    exceeds `usage_limit`, the system will start shortening the history until
    disk usage is brought back within the threshold.
    */
    MONAD_ASSERT(is_on_disk());

    std::tie(compact_offset_fast, compact_offset_slow) =
        deserialize_compaction_offsets(prev_root.value());
    if (version_is_valid_ondisk(version)) {
        return;
    }
    constexpr auto fast_usage_limit_start_compaction = 0.1;
    auto const fast_disk_usage =
        num_chunks(chunk_list::fast) / (double)io->chunk_count();
    if (fast_disk_usage < fast_usage_limit_start_compaction) {
        return;
    }

    MONAD_ASSERT(
        compact_offset_fast != INVALID_COMPACT_VIRTUAL_OFFSET &&
        compact_offset_slow != INVALID_COMPACT_VIRTUAL_OFFSET);
    compact_offset_range_fast_ = MIN_COMPACT_VIRTUAL_OFFSET;

    /* Compact the fast ring based on average disk growth over recent blocks. */
    if (compact_offset_fast < last_block_end_offset_fast_) {
        auto const valid_history_length =
            db_history_max_version() - db_history_min_valid_version() + 1;
        compact_offset_range_fast_.set_value(divide_and_round(
            last_block_end_offset_fast_ - compact_offset_fast,
            valid_history_length));
        compact_offset_fast += compact_offset_range_fast_;
    }
    constexpr double usage_limit_start_compact_slow = 0.6;
    constexpr double slow_usage_limit_start_compact_slow = 0.2;
    auto const slow_list_usage =
        num_chunks(chunk_list::slow) / (double)io->chunk_count();
    // we won't start compacting slow list when slow list usage is low or total
    // usage is below 60%
    if (disk_usage() > usage_limit_start_compact_slow &&
        slow_list_usage > slow_usage_limit_start_compact_slow) {
        // Compact slow ring: the offset is based on slow list garbage
        // collection ratio of last block
        compact_offset_range_slow_.set_value(
            (stats.compacted_bytes_in_slow != 0 &&
             compact_offset_range_slow_ != 0)
                ? std::min(
                      (uint32_t)last_block_disk_growth_slow_ + 1,
                      (uint32_t)std::round(
                          double(compact_offset_range_slow_ << 16) /
                          stats.compacted_bytes_in_slow))
                : 1);
        compact_offset_slow += compact_offset_range_slow_;
    }
    else {
        compact_offset_range_slow_ = MIN_COMPACT_VIRTUAL_OFFSET;
    }
}

uint64_t UpdateAuxImpl::version_history_max_possible() const noexcept
{
    return root_offsets().capacity();
}

uint64_t UpdateAuxImpl::version_history_length() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &db_metadata()->history_length)
        ->load(std::memory_order_relaxed);
}

uint64_t UpdateAuxImpl::db_history_min_valid_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const offsets = root_offsets();
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
        auto version_lower_bound =
            db_metadata()->root_offsets.version_lower_bound_;
        if (max_version - version_lower_bound > version_history_length() + 1) {
            version_lower_bound = max_version - version_history_length() + 1;
        }
        return version_lower_bound;
    }
}

uint64_t UpdateAuxImpl::db_history_max_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return root_offsets().max_version();
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
        chunks_to_remove_before_count_fast_ <=
        db_metadata()->fast_list_end()->insertion_count());
    MONAD_ASSERT(
        chunks_to_remove_before_count_slow_ <=
        db_metadata()->slow_list_end()->insertion_count());
    free_chunks_from_ci_till_count(
        db_metadata()->fast_list_begin(), chunks_to_remove_before_count_fast_);
    free_chunks_from_ci_till_count(
        db_metadata()->slow_list_begin(), chunks_to_remove_before_count_slow_);
}

uint32_t UpdateAuxImpl::num_chunks(chunk_list const list) const noexcept
{
    switch (list) {
    case chunk_list::free:
        // Triggers when out of storage
        MONAD_ASSERT(db_metadata()->free_list_begin() != nullptr);
        MONAD_ASSERT(db_metadata()->free_list_end() != nullptr);

        return (uint32_t)(db_metadata()->free_list_end()->insertion_count() -
                          db_metadata()->free_list_begin()->insertion_count()) +
               1;
    case chunk_list::fast:
        // Triggers when out of storage
        MONAD_ASSERT(db_metadata()->fast_list_begin() != nullptr);
        MONAD_ASSERT(db_metadata()->fast_list_end() != nullptr);

        return (uint32_t)(db_metadata()->fast_list_end()->insertion_count() -
                          db_metadata()->fast_list_begin()->insertion_count()) +
               1;
    case chunk_list::slow:
        // Triggers when out of storage
        MONAD_ASSERT(db_metadata()->slow_list_begin() != nullptr);
        MONAD_ASSERT(db_metadata()->slow_list_end() != nullptr);

        return (uint32_t)(db_metadata()->slow_list_end()->insertion_count() -
                          db_metadata()->slow_list_begin()->insertion_count()) +
               1;
    }
    return 0;
}

void UpdateAuxImpl::print_update_stats(uint64_t const version)
{
#if MONAD_MPT_COLLECT_STATS
    if (stats.nodes_updated_expire > 50'000) {
        LOG_WARNING_CFORMAT(
            "The number of nodes updated for expire (%u) is excessively large",
            stats.nodes_updated_expire);
    }
    char buf[16 << 10];
    char *p = buf;
    p += snprintf(
        p,
        sizeof(buf) - unsigned(p - buf),
        "Version %lu: nodes created or updated for upsert = %u, nodes "
        "updated for expire = %u, nreads for expire = %u\n",
        version,
        stats.nodes_created_or_updated,
        stats.nodes_updated_expire,
        stats.nreads_expire);
    if (compact_offset_range_fast_) {
        p += snprintf(
            p,
            sizeof(buf) - unsigned(p - buf),
            "   Fast: total growth ~ %u KB, compact range %u KB, "
            "bytes copied fast to slow %.2f KB, active data ratio %.2f%%\n",
            last_block_disk_growth_fast_ << 6,
            compact_offset_range_fast_ << 6,
            stats.compacted_bytes_in_fast / 1024.0,
            100.0 * stats.compacted_bytes_in_fast /
                (compact_offset_range_fast_ << 16));
        if (compact_offset_range_slow_) {
            // slow list compaction range vs growth
            auto const total_bytes_written_to_slow =
                stats.compacted_bytes_in_fast + stats.compacted_bytes_in_slow;
            p += snprintf(
                p,
                sizeof(buf) - unsigned(p - buf),
                "   Slow: total growth %.2f KB, compact range %u "
                "KB, bytes copied slow to slow %.2f KB, active data ratio "
                "%.2f%%. other bytes copied slow to fast %.2f KB.\n",
                total_bytes_written_to_slow / 1024.0,
                compact_offset_range_slow_ << 6,
                stats.compacted_bytes_in_slow / 1024.0,
                100.0 * stats.compacted_bytes_in_slow /
                    (compact_offset_range_slow_ << 16),
                stats.bytes_copied_slow_to_fast_for_slow / 1024.0);
        }
        else {
            p += snprintf(
                p,
                sizeof(buf) - unsigned(p - buf),
                "   Slow: no advance of compaction offset\n");
        }

        // num nodes copied:
        auto const nodes_copied_for_slow =
            stats.compacted_nodes_in_fast +
            stats.nodes_copied_fast_to_fast_for_fast;
        p += snprintf(
            p,
            sizeof(buf) - unsigned(p - buf),
            "[Nodes Copied]\n"
            "   Fast: fast to slow %u (%.2f%%), fast to fast %u (%.2f%%)\n",
            stats.compacted_nodes_in_fast,
            nodes_copied_for_slow ? (100.0 * stats.compacted_nodes_in_fast /
                                     (nodes_copied_for_slow))
                                  : 0,
            stats.nodes_copied_fast_to_fast_for_fast,
            nodes_copied_for_slow
                ? (100.0 * stats.nodes_copied_fast_to_fast_for_fast /
                   nodes_copied_for_slow)
                : 0);
        if (compact_offset_slow) {
            auto const nodes_copied_for_slow =
                stats.compacted_nodes_in_slow +
                stats.nodes_copied_fast_to_fast_for_slow +
                stats.nodes_copied_slow_to_fast_for_slow;
            p += snprintf(
                p,
                sizeof(buf) - unsigned(p - buf),
                "   Slow: active slow to slow %u (%.2f%%), fast to fast %u "
                "(%.2f%%), other slow to fast %u (%.2f%%)\n",
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

        p += snprintf(
            p,
            sizeof(buf) - unsigned(p - buf),
            "[Reads]\n"
            "   Fast: compact reads within compaction range %u / "
            "total compact reads %u = %.2f%%\n",
            stats.nreads_before_compact_offset[0],
            stats.nreads_before_compact_offset[0] +
                stats.nreads_after_compact_offset[0],
            stats.nreads_before_compact_offset[0]
                ? (100.0 * stats.nreads_before_compact_offset[0] /
                   (stats.nreads_before_compact_offset[0] +
                    stats.nreads_after_compact_offset[0]))
                : 0);
        p += snprintf(
            p,
            sizeof(buf) - unsigned(p - buf),
            "   Fast: bytes read within compaction range %.2f KB / "
            "compaction range %u KB = %.2f%%, bytes read out of "
            "compaction range %.2f KB\n",
            (double)stats.bytes_read_before_compact_offset[0] / 1024,
            compact_offset_range_fast_ << 6,
            stats.bytes_read_before_compact_offset[0]
                ? (100.0 * stats.bytes_read_before_compact_offset[0] /
                   compact_offset_range_fast_ / 1024 / 64)
                : 0,
            (double)stats.bytes_read_after_compact_offset[0] / 1024);
        if (compact_offset_range_slow_) {
            p += snprintf(
                p,
                sizeof(buf) - unsigned(p - buf),
                "   Slow: reads within compaction range %u / "
                "total compact reads %u = %.2f%%\n",
                stats.nreads_before_compact_offset[1],
                stats.nreads_before_compact_offset[1] +
                    stats.nreads_after_compact_offset[1],
                stats.nreads_before_compact_offset[1]
                    ? (100.0 * stats.nreads_before_compact_offset[1] /
                       (stats.nreads_before_compact_offset[1] +
                        stats.nreads_after_compact_offset[1]))
                    : 0);
            p += snprintf(
                p,
                sizeof(buf) - unsigned(p - buf),
                "   Slow: bytes read within compaction range %.2f KB / "
                "compaction range %u KB = %.2f%%, bytes read out of "
                "compaction range %.2f KB\n",
                (double)stats.bytes_read_before_compact_offset[1] / 1024,
                compact_offset_range_slow_ << 6,
                stats.bytes_read_before_compact_offset[1]
                    ? (100.0 * stats.bytes_read_before_compact_offset[1] /
                       compact_offset_range_slow_ / 1024 / 64)
                    : 0,
                (double)stats.bytes_read_after_compact_offset[1] / 1024);
        }
    }
    LOG_INFO_CFORMAT("%s", buf);
#else
    (void)version;
#endif
}

void UpdateAuxImpl::reset_stats()
{
    stats.reset();
}

void UpdateAuxImpl::collect_number_nodes_created_stats()
{
#if MONAD_MPT_COLLECT_STATS
    ++stats.nodes_created_or_updated;
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

void UpdateAuxImpl::collect_expire_stats(bool const is_read)
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

void UpdateAuxImpl::collect_compacted_nodes_stats(
    bool const copy_node_for_fast, bool const rewrite_to_fast,
    virtual_chunk_offset_t node_offset, uint32_t node_disk_size)
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
                compact_offset_slow);
            ++stats.compacted_nodes_in_slow;
            stats.compacted_bytes_in_slow += node_disk_size;
        }
    }
#else
    if (!copy_node_for_fast && !rewrite_to_fast) {
        MONAD_ASSERT(!node_offset.in_fast_list());
        MONAD_ASSERT(
            compact_virtual_chunk_offset_t{node_offset} < compact_offset_slow);
        stats.compacted_bytes_in_slow += node_disk_size;
    }
    (void)copy_node_for_fast;
    (void)rewrite_to_fast;
#endif
}

MONAD_MPT_NAMESPACE_END
