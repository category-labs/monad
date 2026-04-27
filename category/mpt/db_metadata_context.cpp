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
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/core/log.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <optional>
#include <span>
#include <sys/mman.h>
#include <thread>
#include <unistd.h>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
DbMetadataContext::DbMetadataContext(AsyncIO &io)
    : io_(&io)
{
    auto const chunk_count = io_->chunk_count();
    MONAD_ASSERT(chunk_count >= 3);
    db_map_size_ = sizeof(detail::db_metadata) +
                   chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    auto &cnv_chunk = io_->storage_pool().chunk(storage_pool::cnv, 0);
    auto const fdr = cnv_chunk.read_fd();
    auto const fdw = cnv_chunk.write_fd(0);

    can_write_to_map_ =
        (!io_->storage_pool().is_read_only() ||
         io_->storage_pool().is_read_only_allow_dirty());
    auto const &fd = can_write_to_map_ ? fdw : fdr;
    prot_ = can_write_to_map_ ? (PROT_READ | PROT_WRITE) : (PROT_READ);
    mapflags_ = io_->storage_pool().is_read_only_allow_dirty() ? MAP_PRIVATE
                                                               : MAP_SHARED;

    // mmap both metadata copies
    copies_[0].main = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr, db_map_size_, prot_, mapflags_, fd.first, off_t(fdr.second)));
    MONAD_ASSERT(copies_[0].main != MAP_FAILED);
    copies_[1].main = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        db_map_size_,
        prot_,
        mapflags_,
        fd.first,
        off_t(fdr.second + cnv_chunk.capacity() / 2)));
    MONAD_ASSERT(copies_[1].main != MAP_FAILED);

    // Truncation detection
    if (io_->storage_pool().is_newly_truncated()) {
        memset(copies_[0].main->magic, 0, sizeof(copies_[0].main->magic));
        memset(copies_[1].main->magic, 0, sizeof(copies_[1].main->magic));
    }

    // Magic validation: restore corrupted front copy from backup
    if (0 != memcmp(
                 copies_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (0 == memcmp(
                     copies_[1].main->magic,
                     detail::db_metadata::MAGIC,
                     detail::db_metadata::MAGIC_STRING_LEN)) {
            MONAD_ASSERT(
                can_write_to_map_,
                "First copy of metadata corrupted, but not opened for "
                "healing");
            db_copy(copies_[0].main, copies_[1].main, db_map_size_);
        }
    }

    // Version mismatch detection
    constexpr unsigned magic_version_len = 3;
    constexpr unsigned magic_prefix_len =
        detail::db_metadata::MAGIC_STRING_LEN - magic_version_len;
    if (0 == memcmp(
                 copies_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 magic_prefix_len) &&
        0 != memcmp(
                 copies_[0].main->magic + magic_prefix_len,
                 detail::db_metadata::MAGIC + magic_prefix_len,
                 magic_version_len)) {
        MONAD_ABORT_PRINTF(
            "DB was generated with version %s. The current code base is on "
            "version %s. Please regenerate with the new DB version.",
            copies_[0].main->magic + magic_prefix_len,
            detail::db_metadata::MAGIC + magic_prefix_len);
    }

    // Dirty recovery
    if (0 == memcmp(
                 copies_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN) &&
        0 == memcmp(
                 copies_[1].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (can_write_to_map_) {
            if (copies_[0].main->is_dirty().load(std::memory_order_acquire)) {
                db_copy(copies_[0].main, copies_[1].main, db_map_size_);
            }
            else if (copies_[1].main->is_dirty().load(
                         std::memory_order_acquire)) {
                db_copy(copies_[1].main, copies_[0].main, db_map_size_);
            }
        }
        else {
            if (copies_[0].main->is_dirty().load(std::memory_order_acquire) ||
                copies_[1].main->is_dirty().load(std::memory_order_acquire)) {
                // Wait a bit to see if they clear before complaining
                bool dirty;
                auto const begin = std::chrono::steady_clock::now();
                do {
                    dirty = copies_[0].main->is_dirty().load(
                                std::memory_order_acquire) ||
                            copies_[1].main->is_dirty().load(
                                std::memory_order_acquire);
                    std::this_thread::yield();
                }
                while (dirty && (std::chrono::steady_clock::now() - begin <
                                 std::chrono::seconds(1)));

                MONAD_ASSERT(
                    !dirty,
                    "DB metadata was closed dirty, but not opened for "
                    "healing");
            }
        }
    }

    // Determine if this is a new pool (no valid magic on either copy)
    if (0 != memcmp(
                 copies_[0].main->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        MONAD_ASSERT(
            can_write_to_map_,
            "Neither copy of the DB metadata is valid, and not opened for "
            "writing so stopping now.");
        for (uint32_t n = 0; n < chunk_count; n++) {
            auto const &chunk = io_->storage_pool().chunk(storage_pool::seq, n);
            MONAD_ASSERT(
                chunk.size() == 0,
                "Trying to initialise new DB but storage pool contains "
                "existing data, stopping now to prevent data loss.");
        }
        // Zero metadata, set chunk_info_count
        memset(copies_[0].main, 0, db_map_size_);
        MONAD_ASSERT((chunk_count & ~0xfffffU) == 0);
        copies_[0].main->chunk_info_count = chunk_count & 0xfffffU;

        // Init root_offsets storage cnv chunks
        MONAD_ASSERT(io_->storage_pool().chunks(storage_pool::cnv) > 1);
        auto &storage = copies_[0].main->root_offsets.storage_;
        memset(&storage, 0xff, sizeof(storage));
        storage.cnv_chunks_len = 0;
        auto &chunk = io_->storage_pool().chunk(storage_pool::cnv, 1);
        auto *tofill = aligned_alloc(DISK_PAGE_SIZE, chunk.capacity());
        MONAD_ASSERT(tofill != nullptr);
        auto const untofill =
            monad::make_scope_exit([&]() noexcept { ::free(tofill); });
        memset(tofill, 0xff, chunk.capacity());
        {
            auto const fdw = chunk.write_fd(chunk.capacity());
            MONAD_ASSERT(
                -1 !=
                ::pwrite(
                    fdw.first, tofill, chunk.capacity(), (off_t)fdw.second));
        }
        storage.cnv_chunks[storage.cnv_chunks_len++].cnv_chunk_id = 1;
        copies_[0].main->history_length =
            chunk.capacity() / 2 / sizeof(chunk_offset_t);
        // Allocate cnv chunks of the first device - 1 for root offsets,
        // since chunk 0 is used for db_metadata
        auto const root_offsets_chunk_count =
            io_->storage_pool().devices()[0].cnv_chunks() -
            UpdateAux::cnv_chunks_for_db_metadata;
        MONAD_ASSERT(
            root_offsets_chunk_count > 0 &&
                (root_offsets_chunk_count & (root_offsets_chunk_count - 1)) ==
                    0,
            "Number of cnv chunks for root offsets must be a power of two");
        for (uint32_t n = 2; n <= root_offsets_chunk_count; n++) {
            auto &chunk = io_->storage_pool().chunk(storage_pool::cnv, n);
            auto const fdw = chunk.write_fd(chunk.capacity());
            MONAD_ASSERT(
                -1 !=
                ::pwrite(
                    fdw.first, tofill, chunk.capacity(), (off_t)fdw.second));
            storage.cnv_chunks[storage.cnv_chunks_len++].cnv_chunk_id = n;
            copies_[0].main->history_length +=
                chunk.capacity() / 2 / sizeof(chunk_offset_t);
        }

        is_new_pool_ = true;
    }
    else {
        // Existing pool: map root offsets immediately
        map_root_offsets();
    }
}
#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif

void DbMetadataContext::map_root_offsets()
{
    auto const &cnv_chunk = io_->storage_pool().chunk(storage_pool::cnv, 0);
    size_t const map_bytes_per_chunk = cnv_chunk.capacity() / 2;
    size_t const db_version_history_storage_bytes =
        copies_[0].main->root_offsets.storage_.cnv_chunks_len *
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

    for (size_t n = 0;
         n < copies_[0].main->root_offsets.storage_.cnv_chunks_len;
         n++) {
        auto &chunk = io_->storage_pool().chunk(
            storage_pool::cnv,
            copies_[0].main->root_offsets.storage_.cnv_chunks[n].cnv_chunk_id);
        auto const fdr = chunk.read_fd();
        auto const fdw = chunk.write_fd(0);
        auto const &fd = can_write_to_map_ ? fdw : fdr;
        MONAD_ASSERT(
            MAP_FAILED != ::mmap(
                              reservation[0] + n * map_bytes_per_chunk,
                              map_bytes_per_chunk,
                              prot_,
                              mapflags_ | MAP_FIXED,
                              fd.first,
                              off_t(fdr.second)));
        MONAD_ASSERT(
            MAP_FAILED != ::mmap(
                              reservation[1] + n * map_bytes_per_chunk,
                              map_bytes_per_chunk,
                              prot_,
                              mapflags_ | MAP_FIXED,
                              fd.first,
                              off_t(fdr.second + map_bytes_per_chunk)));
    }
    copies_[0].root_offsets = {
        start_lifetime_as<chunk_offset_t>((chunk_offset_t *)reservation[0]),
        db_version_history_storage_bytes / sizeof(chunk_offset_t)};
    copies_[1].root_offsets = {
        start_lifetime_as<chunk_offset_t>((chunk_offset_t *)reservation[1]),
        db_version_history_storage_bytes / sizeof(chunk_offset_t)};

    LOG_INFO(
        "Database root offsets ring buffer is configured with {} "
        "chunks, can hold up to {} historical entries.",
        copies_[0].main->root_offsets.storage_.cnv_chunks_len,
        copies_[0].root_offsets.size());
}

// Version metadata getters

uint64_t DbMetadataContext::get_latest_finalized_version() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &copies_[0].main->latest_finalized_version)
        ->load(std::memory_order_acquire);
}

uint64_t DbMetadataContext::get_latest_verified_version() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &copies_[0].main->latest_verified_version)
        ->load(std::memory_order_acquire);
}

uint64_t DbMetadataContext::get_latest_voted_version() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &copies_[0].main->latest_voted_version)
        ->load(std::memory_order_acquire);
}

bytes32_t DbMetadataContext::get_latest_voted_block_id() const noexcept
{
    return copies_[0].main->latest_voted_block_id;
}

uint64_t DbMetadataContext::get_latest_proposed_version() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &copies_[0].main->latest_proposed_version)
        ->load(std::memory_order_acquire);
}

bytes32_t DbMetadataContext::get_latest_proposed_block_id() const noexcept
{
    return copies_[0].main->latest_proposed_block_id;
}

int64_t DbMetadataContext::get_auto_expire_version_metadata() const noexcept
{
    return start_lifetime_as<std::atomic_int64_t const>(
               &copies_[0].main->auto_expire_version)
        ->load(std::memory_order_acquire);
}

// Version metadata setters

void DbMetadataContext::set_latest_finalized_version(
    uint64_t const version) noexcept
{
    auto do_ = [&](detail::db_metadata *m) {
        auto const g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_finalized_version)
            ->store(version, std::memory_order_release);
    };
    do_(copies_[0].main);
    do_(copies_[1].main);
}

void DbMetadataContext::set_latest_verified_version(
    uint64_t const version) noexcept
{
    auto do_ = [&](detail::db_metadata *m) {
        auto const g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_verified_version)
            ->store(version, std::memory_order_release);
    };
    do_(copies_[0].main);
    do_(copies_[1].main);
}

void DbMetadataContext::set_latest_voted(
    uint64_t const version, bytes32_t const &block_id) noexcept
{
    for (auto const i : {0, 1}) {
        auto *const m = copies_[i].main;
        auto const g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_voted_version)
            ->store(version, std::memory_order_release);
        m->latest_voted_block_id = block_id;
    }
}

void DbMetadataContext::set_latest_proposed(
    uint64_t const version, bytes32_t const &block_id) noexcept
{
    for (auto const i : {0, 1}) {
        auto *const m = copies_[i].main;
        auto const g = m->hold_dirty();
        reinterpret_cast<std::atomic_uint64_t *>(&m->latest_proposed_version)
            ->store(version, std::memory_order_release);
        m->latest_proposed_block_id = block_id;
    }
}

void DbMetadataContext::set_auto_expire_version_metadata(
    int64_t const version) noexcept
{
    auto do_ = [&](detail::db_metadata *m) {
        auto const g = m->hold_dirty();
        reinterpret_cast<std::atomic_int64_t *>(&m->auto_expire_version)
            ->store(version, std::memory_order_release);
    };
    do_(copies_[0].main);
    do_(copies_[1].main);
}

void DbMetadataContext::update_history_length_metadata(
    uint64_t const history_len) noexcept
{
    auto do_ = [&](unsigned const which) {
        auto *const m = copies_[which].main;
        auto const g = m->hold_dirty();
        auto const ro = root_offsets(which);
        MONAD_ASSERT(history_len > 0 && history_len <= ro.capacity());
        reinterpret_cast<std::atomic_uint64_t *>(&m->history_length)
            ->store(history_len, std::memory_order_relaxed);
    };
    do_(0);
    do_(1);
}

// Root offsets operations

void DbMetadataContext::append_root_offset(
    chunk_offset_t const root_offset) noexcept
{
    auto do_ = [&](unsigned const which) {
        auto const g = copies_[which].main->hold_dirty();
        root_offsets(which).push(root_offset);
    };
    do_(0);
    do_(1);
}

void DbMetadataContext::update_root_offset(
    size_t const i, chunk_offset_t const root_offset) noexcept
{
    auto do_ = [&](unsigned const which) {
        auto const g = copies_[which].main->hold_dirty();
        auto ro = root_offsets(which);
        ro.assign(i, root_offset);
        if (root_offset == INVALID_OFFSET && i == db_history_max_version() &&
            i == db_history_min_valid_version()) {
            ro.reset_all(0);
            MONAD_ASSERT(ro.max_version() == INVALID_BLOCK_NUM);
        }
    };
    do_(0);
    do_(1);
}

void DbMetadataContext::fast_forward_next_version(
    uint64_t const new_version) noexcept
{
    auto do_ = [&](unsigned const which) {
        auto const g = copies_[which].main->hold_dirty();
        auto ro = root_offsets(which);
        uint64_t curr_version = ro.max_version();
        MONAD_ASSERT(
            curr_version == INVALID_BLOCK_NUM || new_version > curr_version);

        if (curr_version == INVALID_BLOCK_NUM ||
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
    do_(0);
    do_(1);
}

void DbMetadataContext::clear_root_offsets_up_to_and_including(
    uint64_t const version)
{
    for (uint64_t v = db_history_range_lower_bound();
         v != INVALID_BLOCK_NUM && v <= version;
         v = db_history_range_lower_bound()) {
        update_root_offset(v, INVALID_OFFSET);
    }
}

// DB offsets

void DbMetadataContext::advance_db_offsets_to(
    chunk_offset_t const fast_offset, chunk_offset_t const slow_offset) noexcept
{
    MONAD_ASSERT(main()->at(fast_offset.id)->in_fast_list);
    MONAD_ASSERT(main()->at(slow_offset.id)->in_slow_list);
    auto do_ = [&](unsigned const which) {
        copies_[which].main->advance_db_offsets_to_(
            detail::db_metadata::db_offsets_info_t{fast_offset, slow_offset});
    };
    do_(0);
    do_(1);
}

// History/version queries

uint64_t DbMetadataContext::version_history_max_possible() const noexcept
{
    return root_offsets().capacity();
}

uint64_t DbMetadataContext::version_history_length() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &copies_[0].main->history_length)
        ->load(std::memory_order_relaxed);
}

uint64_t DbMetadataContext::db_history_min_valid_version() const noexcept
{
    auto const offsets = root_offsets();
    auto min_version = db_history_range_lower_bound();
    for (; min_version != offsets.max_version(); ++min_version) {
        if (offsets[min_version] != INVALID_OFFSET) {
            break;
        }
    }
    return min_version;
}

uint64_t DbMetadataContext::db_history_max_version() const noexcept
{
    return root_offsets().max_version();
}

uint64_t DbMetadataContext::db_history_range_lower_bound() const noexcept
{
    auto const max_version = db_history_max_version();
    if (max_version == INVALID_BLOCK_NUM) {
        return INVALID_BLOCK_NUM;
    }
    else {
        auto const history_range_min =
            max_version >= version_history_length()
                ? (max_version - version_history_length() + 1)
                : 0;
        auto const ro_version_lower_bound =
            copies_[0].main->root_offsets.version_lower_bound_;
        MONAD_ASSERT(ro_version_lower_bound >= history_range_min);
        return ro_version_lower_bound;
    }
}

chunk_offset_t DbMetadataContext::get_root_offset_at_version(
    uint64_t const version) const noexcept
{
    if (version <= db_history_max_version()) {
        auto const offset = root_offsets()[version];
        if (version >= db_history_range_lower_bound()) {
            return offset;
        }
    }
    return INVALID_OFFSET;
}

DbMetadataContext::~DbMetadataContext()
{
    // munmap root_offsets
    for (auto &copy : copies_) {
        if (copy.root_offsets.data() != nullptr) {
            (void)::munmap(
                copy.root_offsets.data(), copy.root_offsets.size_bytes());
            copy.root_offsets = {};
        }
    }
    // munmap db_metadata
    if (copies_[0].main != nullptr) {
        (void)::munmap(copies_[0].main, db_map_size_);
        copies_[0].main = nullptr;
    }
    if (copies_[1].main != nullptr) {
        (void)::munmap(copies_[1].main, db_map_size_);
        copies_[1].main = nullptr;
    }
}

// Define to avoid randomisation of free list chunks on pool creation
// This can be useful to discover bugs in code which assume chunks are
// consecutive
// #define MONAD_MPT_INITIALIZE_POOL_WITH_RANDOM_SHUFFLED_CHUNKS 1
#define MONAD_MPT_INITIALIZE_POOL_WITH_REVERSE_ORDER_CHUNKS 1

void DbMetadataContext::init_new_pool(
    std::optional<uint64_t> const history_len,
    uint32_t const initial_insertion_count)
{
    MONAD_ASSERT(is_new_pool_);
    auto const chunk_count = io_->chunk_count();

    // Init chunk lists
    memset(
        &copies_[0].main->free_list, 0xff, sizeof(copies_[0].main->free_list));
    memset(
        &copies_[0].main->fast_list, 0xff, sizeof(copies_[0].main->fast_list));
    memset(
        &copies_[0].main->slow_list, 0xff, sizeof(copies_[0].main->slow_list));
    auto *chunk_info =
        start_lifetime_as_array<detail::db_metadata::chunk_info_t>(
            copies_[0].main->chunk_info, chunk_count);
    for (size_t n = 0; n < chunk_count; n++) {
        auto &ci = chunk_info[n];
        ci.prev_chunk_id = ci.next_chunk_id =
            detail::db_metadata::chunk_info_t::INVALID_CHUNK_ID;
    }
    // magics are not set yet, so memcpy is fine here
    memcpy(copies_[1].main, copies_[0].main, db_map_size_);

    // Insert all chunks into the free list
    std::vector<uint32_t> chunks;
    chunks.reserve(chunk_count);
    for (uint32_t n = 0; n < chunk_count; n++) {
        auto const chunk = io_->storage_pool().chunk(storage_pool::seq, n);
        MONAD_ASSERT(chunk.zone_id().first == storage_pool::seq);
        MONAD_ASSERT(chunk.zone_id().second == n);
        MONAD_ASSERT(chunk.size() == 0); // chunks must actually be free
        chunks.push_back(n);
    }

#if MONAD_MPT_INITIALIZE_POOL_WITH_REVERSE_ORDER_CHUNKS
    std::reverse(chunks.begin(), chunks.end());
    LOG_INFO_CFORMAT(
        "Initialize db pool with %zu chunks in reverse order.", chunk_count);
#elif MONAD_MPT_INITIALIZE_POOL_WITH_RANDOM_SHUFFLED_CHUNKS
    LOG_INFO_CFORMAT(
        "Initialize db pool with %zu chunks in random order.", chunk_count);
    small_prng rand;
    random_shuffle(chunks.begin(), chunks.end(), rand);
#else
    LOG_INFO_CFORMAT(
        "Initialize db pool with %zu chunks in increasing order.", chunk_count);
#endif
    auto append_with_insertion_count_override = [&](chunk_list list,
                                                    uint32_t id) {
        append(list, id);
        if (initial_insertion_count != 0) {
            auto override_insertion_count = [&](detail::db_metadata *db) {
                auto const g = db->hold_dirty();
                auto *i = db->at_(id);
                i->insertion_count0_ =
                    uint32_t(initial_insertion_count) & 0x3ff;
                i->insertion_count1_ =
                    uint32_t(initial_insertion_count >> 10) & 0x3ff;
            };
            override_insertion_count(copies_[0].main);
            override_insertion_count(copies_[1].main);
        }
        auto *i = copies_[0].main->at_(id);
        MONAD_ASSERT(i->index(copies_[0].main) == id);
    };
    // root offset is the front of fast list
    chunk_offset_t const fast_offset(chunks.front(), 0);
    append_with_insertion_count_override(chunk_list::fast, fast_offset.id);
    LOG_DEBUG_CFORMAT("Append one chunk to fast list, id: %d", fast_offset.id);
    // init the first slow chunk and slow_offset
    chunk_offset_t const slow_offset(chunks[1], 0);
    append_with_insertion_count_override(chunk_list::slow, slow_offset.id);
    LOG_DEBUG_CFORMAT("Append one chunk to slow list, id: %d", slow_offset.id);
    std::span const chunks_after_second(chunks.data() + 2, chunks.size() - 2);
    // insert the rest of the chunks to free list
    for (uint32_t const i : chunks_after_second) {
        append(chunk_list::free, i);
        auto *i_ = copies_[0].main->at_(i);
        MONAD_ASSERT(i_->index(copies_[0].main) == i);
    }

    // Mark as done, init root offset and history versions for the new
    // database as invalid
    advance_db_offsets_to(fast_offset, slow_offset);
    set_latest_finalized_version(INVALID_BLOCK_NUM);
    set_latest_verified_version(INVALID_BLOCK_NUM);
    set_latest_voted(INVALID_BLOCK_NUM, bytes32_t{});
    set_latest_proposed(INVALID_BLOCK_NUM, bytes32_t{});
    set_auto_expire_version_metadata(0);

    for (auto const i : {0, 1}) {
        auto *const m = copies_[i].main;
        auto const g = m->hold_dirty();
        memset(
            m->future_variables_unused,
            0xff,
            sizeof(m->future_variables_unused));
    }

    std::atomic_signal_fence(
        std::memory_order_seq_cst); // no compiler reordering here
    memcpy(
        copies_[0].main->magic,
        detail::db_metadata::MAGIC,
        detail::db_metadata::MAGIC_STRING_LEN);
    memcpy(
        copies_[1].main->magic,
        detail::db_metadata::MAGIC,
        detail::db_metadata::MAGIC_STRING_LEN);

    map_root_offsets();
    // Set history length, MUST be after root offsets are mapped
    if (history_len.has_value()) {
        update_history_length_metadata(*history_len);
    }
}

void DbMetadataContext::append(chunk_list const list, uint32_t const idx)
{
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
    do_(copies_[0].main);
    do_(copies_[1].main);
    if (list == chunk_list::free) {
        auto const &chunk = io_->storage_pool().chunk(storage_pool::seq, idx);
        auto const capacity = chunk.capacity();
        MONAD_ASSERT(chunk.size() == 0);
        copies_[0].main->free_capacity_add_(capacity);
        copies_[1].main->free_capacity_add_(capacity);
    }
    else {
        auto const insertion_count =
            static_cast<uint32_t>(main(0)->at(idx)->insertion_count());
        if (insertion_count >= virtual_chunk_offset_t::MAX_COUNT * 9 / 10) {
            LOG_WARNING_CFORMAT(
                "Virtual offset space is running out "
                "(insertion count: %u / %u). "
                "Please perform a database reset.",
                insertion_count,
                (uint32_t)virtual_chunk_offset_t::MAX_COUNT);
        }
    }
}

void DbMetadataContext::remove(uint32_t const idx) noexcept
{
    bool const is_free_list =
        (!copies_[0].main->at_(idx)->in_fast_list &&
         !copies_[0].main->at_(idx)->in_slow_list);
    auto do_ = [&](detail::db_metadata *m) { m->remove_(m->at_(idx)); };
    do_(copies_[0].main);
    do_(copies_[1].main);
    if (is_free_list) {
        auto const &chunk = io_->storage_pool().chunk(storage_pool::seq, idx);
        auto const capacity = chunk.capacity();
        MONAD_ASSERT(chunk.size() == 0);
        copies_[0].main->free_capacity_sub_(capacity);
        copies_[1].main->free_capacity_sub_(capacity);
    }
}

MONAD_MPT_NAMESPACE_END
