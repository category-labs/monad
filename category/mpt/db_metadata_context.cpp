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
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <array>
#include <atomic>
#include <cerrno>
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
// MONAD007 -> MONAD008 fixed-header offsets used by the in-place migration
// in DbMetadataContext::DbMetadataContext. MONAD007 had
// root_offsets_ring_t::SIZE_ = 65536; MONAD008 dropped it to 32, shrinking
// sizeof(db_metadata) from 528512 to 4480 bytes and shifting chunk_info[]
// and the db_offsets/consensus block accordingly.
static constexpr size_t MONAD007_DB_METADATA_SIZE = 528512;
static constexpr size_t MONAD007_DB_OFFSETS_OFFSET = 524328;
static constexpr size_t MONAD007_DB_OFFSETS_THROUGH_BLOCK_IDS_BYTES = 128;
static constexpr size_t MONAD007_LIST_TRIPLE_OFFSET = 528488;
static constexpr size_t DB_METADATA_LIST_TRIPLE_BYTES = 24;

DbMetadataContext::DbMetadataContext(AsyncIO &io)
    : io_(&io)
{
    auto const chunk_count = io_->chunk_count();
    MONAD_ASSERT(chunk_count >= 3);
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

    // Each copy gets a full half of cnv chunk 0 so the mapping holds any
    // metadata layout (MONAD007's 528 KiB header or MONAD008's 4.4 KiB
    // header) without a pre-mmap magic peek.
    metadata_mmap_size_ = cnv_chunk.capacity() / 2;
    db_map_size_ = sizeof(detail::db_metadata) +
                   chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    MONAD_ASSERT(
        metadata_mmap_size_ >=
            MONAD007_DB_METADATA_SIZE +
                chunk_count * sizeof(detail::db_metadata::chunk_info_t),
        "cnv chunk 0 is too small to hold a MONAD007 metadata header plus "
        "chunk_info[]; pool configuration is incompatible with this build");

    // mmap both metadata copies
    copies_[0].main = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        metadata_mmap_size_,
        prot_,
        mapflags_,
        fd.first,
        off_t(fdr.second)));
    MONAD_ASSERT(copies_[0].main != MAP_FAILED);
    copies_[1].main = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        metadata_mmap_size_,
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

    // Migration: MONAD007 -> MONAD008. The fixed header shrank from
    // 528512 to 4480 bytes; fields adjacent to root_offsets or at the
    // tail of the header moved:
    //
    //   chunk_info[]              528512 -> 4480
    //   free/fast/slow_list triple 528488 -> 4456  (last 24B of header)
    //   db_offsets..latest_proposed_block_id (128B)  524328 -> 312
    //
    // root_offsets and its cnv_chunks[0..30] are byte-identical between
    // layouts. The block now holding root_offsets_state, secondary_timeline,
    // secondary_timeline_state, identity bytes and pending_shrink_grow
    // (offsets 296..4456) was MONAD007 padding and is
    // zeroed so new fields start at idle defaults. Each copy migrates
    // under hold_dirty; the memmove/memcpy/memset operations preserve
    // their sources, so a crash-replay is idempotent.
    auto const is_previous_magic = [](detail::db_metadata const *m) {
        return 0 == memcmp(
                        m->magic,
                        detail::db_metadata::PREVIOUS_MAGIC,
                        detail::db_metadata::MAGIC_STRING_LEN);
    };
    if (is_previous_magic(copies_[0].main) ||
        is_previous_magic(copies_[1].main)) {
        if (!io_->storage_pool().is_migration_allowed()) {
            MONAD_ABORT_PRINTF(
                "DB is on older format (magic=%s) and this binary expects "
                "%s. Run 'monad-mpt --upgrade --storage <path>' before "
                "starting monad services.",
                detail::db_metadata::PREVIOUS_MAGIC,
                detail::db_metadata::MAGIC);
        }
        if (!can_write_to_map_) {
            MONAD_ABORT_PRINTF(
                "Detected pre-dual-timeline DB (magic=%s), which requires "
                "writable mapping to migrate to %s. Open with write access.",
                detail::db_metadata::PREVIOUS_MAGIC,
                detail::db_metadata::MAGIC);
        }
        // Heal any dirty copy from its clean sibling before migration so
        // the loop's hold_dirty cycles can't be confused with a real
        // partial-write signal on a crash. memcpy (not db_copy) because
        // the copies may still be on the previous metadata version.
        for (size_t i = 0; i < 2; ++i) {
            auto *const m = copies_[i].main;
            if (!m->is_dirty().load(std::memory_order_acquire)) {
                continue;
            }
            auto *const o = copies_[1 - i].main;
            MONAD_ASSERT(
                !o->is_dirty().load(std::memory_order_acquire),
                "Both DB metadata copies are dirty — DB is unrecoverable, "
                "restore from backup.");
            (void)memcpy(m, o, metadata_mmap_size_);
        }
        for (auto const &copy : copies_) {
            auto *const m = copy.main;
            if (!is_previous_magic(m)) {
                continue;
            }
            auto const g = m->hold_dirty();
            auto *const m_bytes = reinterpret_cast<std::byte *>(m);

            MONAD_ASSERT(
                m->root_offsets.storage_.cnv_chunks_len <
                    detail::db_metadata::root_offsets_ring_t::SIZE_,
                "MONAD007 pool has more primary cnv chunks than MONAD008's "
                "SIZE_ cap allows — cannot migrate");

            // 1. Stash the list triple (at the tail of the MONAD007
            //    header) before step 2's memmove, whose destination can
            //    overlap the triple's source for chunk_count > 65501.
            std::array<std::byte, DB_METADATA_LIST_TRIPLE_BYTES>
                list_triple_buf{};
            (void)memcpy(
                list_triple_buf.data(),
                m_bytes + MONAD007_LIST_TRIPLE_OFFSET,
                DB_METADATA_LIST_TRIPLE_BYTES);

            // 2. Relocate chunk_info[]. memmove because src/dst may
            //    overlap for pathologically large chunk_count.
            (void)memmove(
                m_bytes + sizeof(detail::db_metadata),
                m_bytes + MONAD007_DB_METADATA_SIZE,
                size_t(chunk_count) *
                    sizeof(detail::db_metadata::chunk_info_t));

            // 3. Install the stashed list triple at its new location.
            (void)memcpy(
                m_bytes + offsetof(detail::db_metadata, free_list),
                list_triple_buf.data(),
                DB_METADATA_LIST_TRIPLE_BYTES);

            // 4. Relocate db_offsets..latest_proposed_block_id, dropping
            //    MONAD007's global auto_expire_version (sandwiched between
            //    latest_proposed_version and latest_voted_block_id) since
            //    MONAD008 promotes it to a per-timeline field in
            //    timeline_state_t. Save the value, then copy the two
            //    halves either side of the gap into the new gap-less
            //    layout.
            static_assert(offsetof(detail::db_metadata, db_offsets) == 312);
            static_assert(
                offsetof(detail::db_metadata, secondary_timeline) == 432);
            constexpr size_t MONAD007_AUTO_EXPIRE_OFFSET =
                MONAD007_DB_OFFSETS_OFFSET + 16 + 5 * 8; // 524384
            constexpr size_t MONAD007_PRE_AUTO_EXPIRE_BYTES =
                MONAD007_AUTO_EXPIRE_OFFSET - MONAD007_DB_OFFSETS_OFFSET; // 56
            constexpr size_t MONAD007_POST_AUTO_EXPIRE_BYTES =
                MONAD007_DB_OFFSETS_THROUGH_BLOCK_IDS_BYTES -
                MONAD007_PRE_AUTO_EXPIRE_BYTES - 8; // 64
            int64_t saved_auto_expire = 0;
            (void)memcpy(
                &saved_auto_expire,
                m_bytes + MONAD007_AUTO_EXPIRE_OFFSET,
                sizeof(saved_auto_expire));
            (void)memcpy(
                m_bytes + offsetof(detail::db_metadata, db_offsets),
                m_bytes + MONAD007_DB_OFFSETS_OFFSET,
                MONAD007_PRE_AUTO_EXPIRE_BYTES);
            (void)memcpy(
                m_bytes + offsetof(detail::db_metadata, latest_voted_block_id),
                m_bytes + MONAD007_AUTO_EXPIRE_OFFSET + 8,
                MONAD007_POST_AUTO_EXPIRE_BYTES);
            // MONAD007 had no secondary, so the saved value belongs on
            // what is now the primary.
            m->root_offsets_state.auto_expire_version_ = saved_auto_expire;
            // The bytes overlapping
            // root_offsets_state.reserved_for_future_fields_ were inside
            // MONAD007's huge cnv_chunks[] array (filled with 0xff for unused
            // slots). Zero them so subsequent PRs adding fields to
            // timeline_state_t start from a clean slate.
            memset(
                m->root_offsets_state.reserved_for_future_fields_,
                0,
                sizeof(m->root_offsets_state.reserved_for_future_fields_));

            // 5. Zero the region between secondary_timeline and the live
            //    block list (relocated in step 3).
            auto *const new_fields_begin =
                m_bytes + offsetof(detail::db_metadata, secondary_timeline);
            auto *const new_fields_end =
                m_bytes + offsetof(detail::db_metadata, free_list);
            memset(
                new_fields_begin, 0, size_t(new_fields_end - new_fields_begin));

            // 6. Bump magic. The signal_fence keeps the preceding stores
            //    from sinking past it under -O3 reordering; durability is
            //    enforced by the msync after the loop.
            std::atomic_signal_fence(std::memory_order_seq_cst);
            memcpy(
                m->magic,
                detail::db_metadata::MAGIC,
                detail::db_metadata::MAGIC_STRING_LEN);
        }
        // Flush the new layout before downstream code reads at the new
        // offsets.
        sync_metadata_to_disk_();
        LOG_INFO(
            "Migrated DB metadata from {} to {}.",
            detail::db_metadata::PREVIOUS_MAGIC,
            detail::db_metadata::MAGIC);
    }

    // Version mismatch detection (for any other version that we don't migrate)
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

        // All cnv ring chunks go to ring_a; ring_b receives its half on
        // activate_secondary_header.
        uint32_t const cnv_chunks_total = static_cast<uint32_t>(
            io_->storage_pool().devices()[0].cnv_chunks());
        MONAD_ASSERT(cnv_chunks_total > UpdateAux::cnv_chunks_for_db_metadata);
        uint32_t const ring_total =
            cnv_chunks_total - UpdateAux::cnv_chunks_for_db_metadata;
        MONAD_ASSERT(
            ring_total > 0 && (ring_total & (ring_total - 1)) == 0,
            "Number of cnv chunks for root offsets must be a power of two");

        auto &a_storage = copies_[0].main->root_offsets.storage_;
        auto &b_storage = copies_[0].main->secondary_timeline.storage_;
        memset(&a_storage, 0xff, sizeof(a_storage));
        memset(&b_storage, 0xff, sizeof(b_storage));
        a_storage.cnv_chunks_len = 0;
        b_storage.cnv_chunks_len = 0;

        auto const &first_chunk =
            io_->storage_pool().chunk(storage_pool::cnv, 1);
        auto *tofill = aligned_alloc(DISK_PAGE_SIZE, first_chunk.capacity());
        MONAD_ASSERT(tofill != nullptr);
        auto const untofill =
            monad::make_scope_exit([&]() noexcept { ::free(tofill); });
        memset(tofill, 0xff, first_chunk.capacity());

        for (uint32_t n = 1; n <= ring_total; n++) {
            auto &chunk = io_->storage_pool().chunk(storage_pool::cnv, n);
            auto const fdw = chunk.write_fd(chunk.capacity());
            MONAD_ASSERT(
                -1 !=
                ::pwrite(
                    fdw.first, tofill, chunk.capacity(), (off_t)fdw.second));
            a_storage.cnv_chunks[a_storage.cnv_chunks_len++].cnv_chunk_id = n;
        }

        copies_[0].main->history_length =
            static_cast<uint64_t>(ring_total) *
            (first_chunk.capacity() / 2 / sizeof(chunk_offset_t));

        is_new_pool_ = true;
    }
    else {
        map_ring_a_storage();
        map_ring_b_storage();
        replay_pending_shrink_grow_();
    }
}
#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif

void DbMetadataContext::map_ring_a_storage()
{
    map_ring_storage_(
        copies_[0].main->root_offsets.storage_, &metadata_copy::ring_a_span);
    LOG_INFO(
        "Database ring_a is configured with {} chunks (of {} max)",
        copies_[0].main->root_offsets.storage_.cnv_chunks_len,
        ring_max_chunks_());
}

void DbMetadataContext::map_ring_b_storage()
{
    map_ring_storage_(
        copies_[0].main->secondary_timeline.storage_,
        &metadata_copy::ring_b_span);
    LOG_INFO(
        "Database ring_b is configured with {} chunks (of {} max)",
        copies_[0].main->secondary_timeline.storage_.cnv_chunks_len,
        ring_max_chunks_());
}

uint32_t DbMetadataContext::ring_max_chunks_() const noexcept
{
    return static_cast<uint32_t>(
               io_->storage_pool().devices()[0].cnv_chunks()) -
           1 /* chunk 0 holds db_metadata */;
}

size_t DbMetadataContext::map_bytes_per_chunk_() const noexcept
{
    return io_->storage_pool().chunk(storage_pool::cnv, 0).capacity() / 2;
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

int64_t DbMetadataContext::get_auto_expire_version_metadata(
    timeline_id const tid) const noexcept
{
    auto const *const m = copies_[0].main;
    uint8_t const primary_idx = primary_ring_idx();
    uint8_t const ring_idx = (tid == timeline_id::primary)
                                 ? primary_idx
                                 : static_cast<uint8_t>(primary_idx ^ 1u);
    auto const *const slot =
        (ring_idx == 0) ? &m->root_offsets_state.auto_expire_version_
                        : &m->secondary_timeline_state.auto_expire_version_;
    return start_lifetime_as<std::atomic_int64_t const>(slot)->load(
        std::memory_order_acquire);
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
    timeline_id const tid, int64_t const version) noexcept
{
    uint8_t const primary_idx = primary_ring_idx();
    uint8_t const ring_idx = (tid == timeline_id::primary)
                                 ? primary_idx
                                 : static_cast<uint8_t>(primary_idx ^ 1u);
    auto do_ = [&](detail::db_metadata *m) {
        auto const g = m->hold_dirty();
        auto *const slot =
            (ring_idx == 0) ? &m->root_offsets_state.auto_expire_version_
                            : &m->secondary_timeline_state.auto_expire_version_;
        start_lifetime_as<std::atomic_int64_t>(slot)->store(
            version, std::memory_order_release);
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

uint64_t DbMetadataContext::db_history_range_lower_bound(
    timeline_id const tid) const noexcept
{
    if (!timeline_active(tid)) {
        return INVALID_BLOCK_NUM;
    }
    auto const ro = root_offsets(tid);
    if (ro.max_version() == INVALID_BLOCK_NUM) {
        return INVALID_BLOCK_NUM;
    }
    return ro.version_lower_bound();
}

uint64_t DbMetadataContext::db_history_range_lower_bound() const noexcept
{
    return db_history_range_lower_bound(timeline_id::primary);
}

bool DbMetadataContext::timeline_active(timeline_id const tid) const noexcept
{
    if (tid == timeline_id::primary) {
        return true;
    }
    return start_lifetime_as<std::atomic<uint8_t> const>(
               &copies_[0].main->secondary_timeline_active_)
               ->load(std::memory_order_acquire) != 0;
}

chunk_offset_t DbMetadataContext::get_root_offset_at_version(
    uint64_t const version, timeline_id const tid) const noexcept
{
    // Capacity changes only via the offline-only shrink/grow operations, so
    // no concurrent activate/deactivate can move the ring under this read.
    if (!timeline_active(tid)) {
        return INVALID_OFFSET;
    }
    auto const ro = root_offsets(tid);
    auto const lower_bound = db_history_range_lower_bound(tid);
    if (lower_bound == INVALID_BLOCK_NUM || version < lower_bound ||
        version > ro.max_version()) {
        return INVALID_OFFSET;
    }
    return ro[version];
}

chunk_offset_t DbMetadataContext::get_root_offset_at_version(
    uint64_t const version) const noexcept
{
    return get_root_offset_at_version(version, timeline_id::primary);
}

uint64_t
DbMetadataContext::db_history_max_version(timeline_id const tid) const noexcept
{
    if (!timeline_active(tid)) {
        return INVALID_BLOCK_NUM;
    }
    return root_offsets(tid).max_version();
}

uint64_t DbMetadataContext::db_history_max_version() const noexcept
{
    return db_history_max_version(timeline_id::primary);
}

uint64_t DbMetadataContext::db_history_min_valid_version(
    timeline_id const tid) const noexcept
{
    return db_history_range_lower_bound(tid);
}

uint64_t DbMetadataContext::db_history_min_valid_version() const noexcept
{
    return db_history_min_valid_version(timeline_id::primary);
}

namespace
{
    // MAP_FIXED a single cnv chunk into the next free slot of the ring's
    // pre-reserved VA. The chunk may already be mapped into this VA (from
    // a previous activate/deactivate cycle or from map_ring_*_storage at
    // startup); MAP_FIXED is idempotent in that case and just re-installs
    // the same backing page.
    void install_chunk_mapping_(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io, std::span<chunk_offset_t> ring_span,
        size_t slot_index, uint32_t cnv_chunk_id, size_t map_bytes, int prot,
        int mapflags, bool can_write, bool second_copy)
    {
        auto &chunk = io.storage_pool().chunk(
            MONAD_ASYNC_NAMESPACE::storage_pool::cnv, cnv_chunk_id);
        auto const fdr = chunk.read_fd();
        auto const fdw = chunk.write_fd(0);
        auto const &fd = can_write ? fdw : fdr;
        auto *target = reinterpret_cast<std::byte *>(ring_span.data()) +
                       slot_index * map_bytes;
        auto const file_offset =
            second_copy ? off_t(fdr.second + map_bytes) : off_t(fdr.second);
        MONAD_ASSERT_PRINTF(
            MAP_FAILED != ::mmap(
                              target,
                              map_bytes,
                              prot,
                              mapflags | MAP_FIXED,
                              fd.first,
                              file_offset),
            "MAP_FIXED failed for cnv chunk %u slot %zu (second_copy=%d): %s "
            "(errno=%d)",
            cnv_chunk_id,
            slot_index,
            int(second_copy),
            strerror(errno),
            errno);
    }
}

void DbMetadataContext::replay_pending_shrink_grow_()
{
    auto const op0 = copies_[0].main->pending_shrink_grow.op_kind;
    auto const op1 = copies_[1].main->pending_shrink_grow.op_kind;
    if (op0 == detail::db_metadata::PENDING_OP_NONE &&
        op1 == detail::db_metadata::PENDING_OP_NONE) {
        return;
    }
    MONAD_ASSERT(
        can_write_to_map_,
        "DB metadata has a pending shrink/grow op from a prior crash, but "
        "the DB was not opened for healing. Reopen read-write to recover.");
    // Defend against disagreement: the stamp writes identical values to
    // both copies, so any mismatch between non-NONE records is out-of-
    // band corruption or a protocol regression. Abort rather than
    // silently picking one copy's params and applying them to ring data
    // that the other copy might have already committed under different
    // params.
    if (op0 != detail::db_metadata::PENDING_OP_NONE &&
        op1 != detail::db_metadata::PENDING_OP_NONE) {
        MONAD_ASSERT(
            0 == memcmp(
                     &copies_[0].main->pending_shrink_grow,
                     &copies_[1].main->pending_shrink_grow,
                     sizeof(detail::db_metadata::pending_shrink_grow_t)),
            "pending_shrink_grow disagrees between metadata copies");
    }
    // Use whichever copy has the flag set. The single-side case arises
    // when a crash landed between the two per-copy hold_dirty scopes in
    // either set_pending_shrink_grow_ (the first scope finished, the
    // second hadn't started) or clear_pending_shrink_grow_ (one scope
    // cleared, the other hadn't), and neither copy was dirty at crash
    // time so the dirty-bit path didn't propagate. Replay is idempotent
    // and clears the flag on both copies at the end.
    auto const &pending = (op0 != detail::db_metadata::PENDING_OP_NONE)
                              ? copies_[0].main->pending_shrink_grow
                              : copies_[1].main->pending_shrink_grow;
    auto const op_kind = pending.op_kind;
    auto const op_param = pending.op_param;
    if (op_kind == detail::db_metadata::PENDING_OP_ACTIVATE) {
        LOG_INFO(
            "Replaying in-flight activate_secondary_header (target primary "
            "chunks = {}) after unclean shutdown",
            op_param);
        do_activate_secondary_body_(op_param);
    }
    else if (op_kind == detail::db_metadata::PENDING_OP_DEACTIVATE) {
        LOG_INFO(
            "Replaying in-flight deactivate_secondary_header (target "
            "primary chunks = {}) after unclean shutdown",
            op_param);
        do_deactivate_secondary_body_(op_param);
    }
    else if (op_kind == detail::db_metadata::PENDING_OP_PROMOTE) {
        LOG_INFO(
            "Replaying in-flight promote_secondary_to_primary_header (target "
            "primary_ring_idx = {}) after unclean shutdown",
            op_param);
        do_promote_secondary_to_primary_body_(static_cast<uint8_t>(op_param));
    }
    else {
        MONAD_ABORT_PRINTF(
            "Unknown pending_shrink_grow op_kind %u in metadata; DB may be "
            "from a newer code version",
            op_kind);
    }
    sync_ring_data_to_disk_();
    sync_metadata_to_disk_();
    clear_pending_shrink_grow_();
    sync_metadata_to_disk_();
}

void DbMetadataContext::sync_metadata_to_disk()
{
    sync_metadata_to_disk_();
}

void DbMetadataContext::sync_metadata_to_disk_()
{
    MONAD_ASSERT(can_write_to_map_);
    for (unsigned which = 0; which < 2; which++) {
        MONAD_ASSERT_PRINTF(
            0 == ::msync(copies_[which].main, db_map_size_, MS_SYNC),
            "msync of metadata copy %u failed: %s (errno=%d)",
            which,
            strerror(errno),
            errno);
    }
    // Also fsync the underlying cnv chunk 0 FD so the filesystem journal
    // commits the msync'd pages (msync's durability guarantees across
    // filesystems/kernels are narrower than fsync's).
    auto &cnv_chunk_0 =
        io_->storage_pool().chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
    auto const fdw = cnv_chunk_0.write_fd(0);
    MONAD_ASSERT_PRINTF(
        0 == ::fsync(fdw.first),
        "fsync of cnv chunk 0 failed: %s (errno=%d)",
        strerror(errno),
        errno);
}

void DbMetadataContext::sync_ring_data_to_disk_()
{
    MONAD_ASSERT(can_write_to_map_);
    // Sync only the currently-live prefix of each ring. Tail slots are
    // PROT_NONE anonymous reservations and need not be msync'd. If a
    // ring has chunks but the span is null, that's a construction-time
    // invariant violation — assert rather than silently skipping.
    auto const sync_ring = [this](
                               std::span<chunk_offset_t> span,
                               uint32_t chunks_len,
                               char const *ring_name,
                               unsigned which) {
        if (chunks_len == 0) {
            return;
        }
        MONAD_ASSERT_PRINTF(
            span.data() != nullptr,
            "%s has %u chunks but no mapping on copy %u",
            ring_name,
            chunks_len,
            which);
        auto const bytes = uint64_t(chunks_len) * map_bytes_per_chunk_();
        MONAD_ASSERT_PRINTF(
            0 == ::msync(span.data(), bytes, MS_SYNC),
            "msync of %s on copy %u (%lu bytes) failed: %s (errno=%d)",
            ring_name,
            which,
            bytes,
            strerror(errno),
            errno);
    };
    for (unsigned which = 0; which < 2; which++) {
        auto *const m = copies_[which].main;
        sync_ring(
            copies_[which].ring_a_span,
            m->root_offsets.storage_.cnv_chunks_len,
            "ring_a",
            which);
        sync_ring(
            copies_[which].ring_b_span,
            m->secondary_timeline.storage_.cnv_chunks_len,
            "ring_b",
            which);
    }
    // Ring data lives in cnv chunks 1..N. Issue fsync on each chunk's FD
    // that currently backs any ring slot. We consult copy 0's cnv_chunks
    // lists as the source of truth (both copies are synchronised under
    // the dual-copy protocol; any chunk id that is valid in one copy is
    // valid in the other too).
    auto const fsync_chunks =
        [this](detail::db_metadata::root_offsets_ring_t const &ring) {
            auto const len = ring.storage_.cnv_chunks_len;
            for (uint32_t k = 0; k < len; k++) {
                auto const id = ring.storage_.cnv_chunks[k].cnv_chunk_id;
                if (id == detail::db_metadata::NULL_CHUNK) {
                    continue;
                }
                auto &chunk = io_->storage_pool().chunk(
                    MONAD_ASYNC_NAMESPACE::storage_pool::cnv, id);
                auto const fdw = chunk.write_fd(0);
                MONAD_ASSERT_PRINTF(
                    0 == ::fsync(fdw.first),
                    "fsync of cnv chunk %u failed: %s (errno=%d)",
                    id,
                    strerror(errno),
                    errno);
            }
        };
    fsync_chunks(copies_[0].main->root_offsets);
    fsync_chunks(copies_[0].main->secondary_timeline);
}

void DbMetadataContext::set_pending_shrink_grow_(
    detail::db_metadata::pending_op_kind const op_kind, uint32_t const op_param)
{
    MONAD_ASSERT(op_kind != detail::db_metadata::PENDING_OP_NONE);
    // Two crash windows this design tolerates:
    //   (a) Inside a single copy's hold_dirty scope: that copy is dirty,
    //       dirty-bit recovery on reopen restores it from the other
    //       (clean) copy, yielding "both not-stamped" or "both stamped"
    //       depending on which was mid-write.
    //   (b) Between the two per-copy scopes (copy 0 stamped and clean,
    //       copy 1 unstamped and clean): neither is dirty, dirty-bit
    //       recovery does nothing, but replay fires whenever EITHER
    //       copy has op_kind != NONE, and replay is idempotent.
    for (auto const &copy : copies_) {
        auto *const m = copy.main;
        auto const g = m->hold_dirty();
        m->pending_shrink_grow.op_kind = static_cast<uint32_t>(op_kind);
        m->pending_shrink_grow.op_param = op_param;
    }
}

void DbMetadataContext::clear_pending_shrink_grow_()
{
    for (auto const &copy : copies_) {
        auto *const m = copy.main;
        auto const g = m->hold_dirty();
        m->pending_shrink_grow.op_kind = detail::db_metadata::PENDING_OP_NONE;
        m->pending_shrink_grow.op_param = 0;
    }
}

void DbMetadataContext::do_activate_secondary_body_(uint32_t const new_chunks)
{
    uint8_t const primary_idx = primary_ring_idx();
    uint8_t const secondary_idx = primary_idx ^ 1u;

    auto const entries_per_chunk =
        map_bytes_per_chunk_() / sizeof(chunk_offset_t);
    uint64_t const new_cap = uint64_t(new_chunks) * entries_per_chunk;

    for (unsigned which = 0; which < 2; which++) {
        auto *const m = copies_[which].main;
        auto const g = m->hold_dirty();
        auto &pstore = (primary_idx == 0) ? m->root_offsets.storage_
                                          : m->secondary_timeline.storage_;
        auto &sstore = (primary_idx == 0) ? m->secondary_timeline.storage_
                                          : m->root_offsets.storage_;
        auto *pver_lb = (primary_idx == 0)
                            ? &m->root_offsets.version_lower_bound_
                            : &m->secondary_timeline.version_lower_bound_;
        auto *pver_nv = (primary_idx == 0)
                            ? &m->root_offsets.next_version_
                            : &m->secondary_timeline.next_version_;
        auto *sver_lb = (primary_idx == 0)
                            ? &m->secondary_timeline.version_lower_bound_
                            : &m->root_offsets.version_lower_bound_;
        auto *sver_nv = (primary_idx == 0)
                            ? &m->secondary_timeline.next_version_
                            : &m->root_offsets.next_version_;
        auto const &pring = copies_[which];
        auto const primary_span =
            (primary_idx == 0) ? pring.ring_a_span : pring.ring_b_span;
        auto const secondary_span =
            (secondary_idx == 0) ? pring.ring_a_span : pring.ring_b_span;

        // Derive old_chunks from this copy's current primary cnv_chunks_len.
        // Under replay, this may already equal new_chunks (commit durable)
        // or still equal new_chunks * 2 (pre-commit); both are handled
        // uniformly by the step-by-step idempotency guards below.
        uint32_t const cur_primary_chunks = pstore.cnv_chunks_len;
        MONAD_ASSERT(
            cur_primary_chunks == new_chunks ||
            cur_primary_chunks == new_chunks * 2);
        uint32_t const old_chunks = (cur_primary_chunks == new_chunks)
                                        ? new_chunks * 2
                                        : cur_primary_chunks;
        uint64_t const old_cap = uint64_t(old_chunks) * entries_per_chunk;

        // 1. Bump primary's version_lower_bound_ if the new (smaller)
        //    capacity excludes older versions (idempotent: std::max is a
        //    fixed point under repeated application).
        uint64_t const nv =
            start_lifetime_as<std::atomic_uint64_t const>(pver_nv)->load(
                std::memory_order_acquire);
        uint64_t const cur_lb =
            start_lifetime_as<std::atomic_uint64_t const>(pver_lb)->load(
                std::memory_order_acquire);
        uint64_t const new_lb =
            std::max(cur_lb, (nv >= new_cap) ? (nv - new_cap) : uint64_t{0});
        if (new_lb > cur_lb) {
            start_lifetime_as<std::atomic_uint64_t>(pver_lb)->store(
                new_lb, std::memory_order_release);
        }
        // 2. Under replay, the primary's tail slots [new_chunks, old_chunks)
        //    may have been left PROT_NONE by map_ring_a/b_storage if a
        //    prior crashed run cleared pstore.cnv_chunks[k].cnv_chunk_id
        //    (step 4 below) before the cnv_chunks_len commit (step 6). The
        //    ring-copy loop at step 3 reads from those slots, so remap
        //    them here first — derive each chunk id from pstore (if still
        //    populated) or sstore (if already swapped over). MAP_FIXED is
        //    idempotent on the fresh-run path where pstore is fully
        //    populated and the VA is already mapped.
        if (cur_primary_chunks == old_chunks) {
            for (uint32_t k = new_chunks; k < old_chunks; k++) {
                uint32_t chunk_id = pstore.cnv_chunks[k].cnv_chunk_id;
                if (chunk_id == detail::db_metadata::NULL_CHUNK) {
                    chunk_id = sstore.cnv_chunks[k - new_chunks].cnv_chunk_id;
                }
                MONAD_ASSERT(chunk_id != detail::db_metadata::NULL_CHUNK);
                install_chunk_mapping_(
                    *io_,
                    primary_span,
                    k,
                    chunk_id,
                    map_bytes_per_chunk_(),
                    prot_,
                    mapflags_,
                    can_write_to_map_,
                    /*second_copy=*/which == 1);
            }
        }
        // 3. Copy kept entries from old positions to new positions on the
        //    primary ring. Source range [new_cap, old_cap) and destination
        //    range [0, new_cap) are disjoint and sources are never written,
        //    so the loop is idempotent under replay.
        if (cur_primary_chunks == old_chunks) {
            for (uint64_t v = new_lb; v < nv; v++) {
                uint64_t const old_pos = v & (old_cap - 1);
                uint64_t const new_pos = v & (new_cap - 1);
                if (old_pos == new_pos) {
                    continue;
                }
                auto *src = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &primary_span[old_pos]);
                auto *dst = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &primary_span[new_pos]);
                dst->store(
                    src->load(std::memory_order_acquire),
                    std::memory_order_release);
            }
        }
        // 4. Install MAP_FIXED mappings for secondary's chunks BEFORE the
        //    cnv_chunks[] swap. If a mmap failure aborts us here,
        //    cnv_chunks[] state is still whole, so recovery remains
        //    unambiguous. MAP_FIXED is idempotent. Derive each chunk id
        //    either from sstore (already moved by a prior partial run)
        //    or from pstore's tail (not yet moved).
        for (uint32_t k = 0; k < new_chunks; k++) {
            uint32_t chunk_id = sstore.cnv_chunks[k].cnv_chunk_id;
            if (chunk_id == detail::db_metadata::NULL_CHUNK) {
                chunk_id = pstore.cnv_chunks[new_chunks + k].cnv_chunk_id;
            }
            MONAD_ASSERT(chunk_id != detail::db_metadata::NULL_CHUNK);
            install_chunk_mapping_(
                *io_,
                secondary_span,
                k,
                chunk_id,
                map_bytes_per_chunk_(),
                prot_,
                mapflags_,
                can_write_to_map_,
                /*second_copy=*/which == 1);
        }
        // 5. Transfer the second half of chunks from primary to secondary.
        //    Idempotent: a destination slot that already holds a valid
        //    chunk id is the "already moved" signal — skip it.
        for (uint32_t k = 0; k < new_chunks; k++) {
            if (sstore.cnv_chunks[k].cnv_chunk_id !=
                detail::db_metadata::NULL_CHUNK) {
                continue;
            }
            auto const moved_id =
                pstore.cnv_chunks[new_chunks + k].cnv_chunk_id;
            MONAD_ASSERT(moved_id != detail::db_metadata::NULL_CHUNK);
            sstore.cnv_chunks[k].high_bits_all_set = uint32_t(-1);
            sstore.cnv_chunks[k].cnv_chunk_id = moved_id;
            pstore.cnv_chunks[new_chunks + k].cnv_chunk_id =
                detail::db_metadata::NULL_CHUNK;
        }
        // 6. Initialise the secondary ring (INVALID_OFFSET fill, then
        //    zero version fields). The secondary timeline starts empty —
        //    next_version_ == 0 maps to INVALID_BLOCK_NUM, which signals
        //    fast_forward_next_version to seed both version fields when the
        //    secondary writes its first root. Safe to re-run during replay
        //    because replay executes in the constructor before any client
        //    thread can observe the DB, and the live-path
        //    `activate_secondary_header` is synchronous — no client can
        //    push to the secondary ring until the public call has returned,
        //    at which point the pending flag has already been cleared +
        //    msync'd.
        auto const secondary_live_bytes =
            uint64_t(new_chunks) * map_bytes_per_chunk_();
        memset((void *)secondary_span.data(), 0xff, secondary_live_bytes);
        start_lifetime_as<std::atomic_uint64_t>(sver_lb)->store(
            0, std::memory_order_release);
        start_lifetime_as<std::atomic_uint64_t>(sver_nv)->store(
            0, std::memory_order_release);
        // 7. Commit cnv_chunks_len (idempotent store of the same value).
        start_lifetime_as<std::atomic<uint32_t>>(&pstore.cnv_chunks_len)
            ->store(new_chunks, std::memory_order_release);
        start_lifetime_as<std::atomic<uint32_t>>(&sstore.cnv_chunks_len)
            ->store(new_chunks, std::memory_order_release);
        // 8. Flip secondary_timeline_active_ (idempotent).
        start_lifetime_as<std::atomic<uint8_t>>(&m->secondary_timeline_active_)
            ->store(1, std::memory_order_release);
    }

    if (version_history_length() > new_cap) {
        update_history_length_metadata(std::max(new_cap, MIN_HISTORY_LENGTH));
    }
}

void DbMetadataContext::activate_secondary_header()
{
    MONAD_ASSERT(!timeline_active(timeline_id::secondary));
    MONAD_ASSERT(
        copies_[0].main->pending_shrink_grow.op_kind ==
            detail::db_metadata::PENDING_OP_NONE &&
        copies_[1].main->pending_shrink_grow.op_kind ==
            detail::db_metadata::PENDING_OP_NONE);

    uint8_t const primary_idx = primary_ring_idx();
    auto const &primary_storage =
        (primary_idx == 0) ? copies_[0].main->root_offsets.storage_
                           : copies_[0].main->secondary_timeline.storage_;
    auto const old_chunks = primary_storage.cnv_chunks_len;
    MONAD_ASSERT(
        old_chunks >= 2 && (old_chunks & (old_chunks - 1)) == 0,
        "activate_secondary_header requires the primary ring to have at "
        "least 2 chunks (power of 2) so it can be split in half");
    uint32_t const new_chunks = old_chunks / 2;

    // Stamp the intent log and make it durable before touching anything.
    // On crash anywhere below, replay in the constructor will run the
    // idempotent body again and clear the flag. Without this the kernel
    // could flush ring-chunk pages before the metadata page, producing
    // a durable "new ring data + old capacity" state that is corrupt
    // (readers mask with old_cap into destinations holding new data).
    set_pending_shrink_grow_(
        detail::db_metadata::PENDING_OP_ACTIVATE, new_chunks);
    sync_metadata_to_disk_();

    do_activate_secondary_body_(new_chunks);

    // Make the body durable before clearing the intent flag. If the
    // flag-clear reached disk before the ring data, a crash here would
    // produce "new metadata, stale ring data" with no flag to trigger
    // replay.
    sync_ring_data_to_disk_();
    sync_metadata_to_disk_();

    clear_pending_shrink_grow_();
    sync_metadata_to_disk_();

    LOG_INFO(
        "Activated secondary timeline (primary ring shrunk from {} to {} "
        "chunks; secondary gained {} chunks)",
        old_chunks,
        new_chunks,
        new_chunks);
}

void DbMetadataContext::do_deactivate_secondary_body_(
    uint32_t const primary_new_chunks)
{
    uint8_t const primary_idx = primary_ring_idx();

    auto const entries_per_chunk =
        map_bytes_per_chunk_() / sizeof(chunk_offset_t);
    uint64_t const new_cap = uint64_t(primary_new_chunks) * entries_per_chunk;

    for (unsigned which = 0; which < 2; which++) {
        auto *const m = copies_[which].main;
        auto const g = m->hold_dirty();
        auto &pstore = (primary_idx == 0) ? m->root_offsets.storage_
                                          : m->secondary_timeline.storage_;
        auto &sstore = (primary_idx == 0) ? m->secondary_timeline.storage_
                                          : m->root_offsets.storage_;
        auto *pver_lb = (primary_idx == 0)
                            ? &m->root_offsets.version_lower_bound_
                            : &m->secondary_timeline.version_lower_bound_;
        auto *pver_nv = (primary_idx == 0)
                            ? &m->root_offsets.next_version_
                            : &m->secondary_timeline.next_version_;
        auto const &pring = copies_[which];
        auto const primary_span =
            (primary_idx == 0) ? pring.ring_a_span : pring.ring_b_span;

        // Under replay, pstore.cnv_chunks_len is either the pre-op size
        // (commit not yet durable) or primary_new_chunks (already
        // committed). The pre-op size is always exactly half of
        // primary_new_chunks because deactivate always doubles a
        // power-of-two primary ring by returning the secondary's chunks
        // that activate symmetrically split off. Any other value
        // indicates metadata corruption — abort rather than compute ring
        // masks from a non-power-of-two capacity.
        uint32_t const cur_primary_chunks = pstore.cnv_chunks_len;
        MONAD_ASSERT(
            cur_primary_chunks == primary_new_chunks ||
            cur_primary_chunks * 2 == primary_new_chunks);
        uint32_t const primary_old_chunks =
            (cur_primary_chunks == primary_new_chunks) ? primary_new_chunks
                                                       : cur_primary_chunks;
        uint32_t const returning_chunks =
            primary_new_chunks - primary_old_chunks;
        uint64_t const old_cap =
            uint64_t(primary_old_chunks) * entries_per_chunk;

        // 1. Install MAP_FIXED mappings for returning chunks BEFORE the
        //    cnv_chunks[] swap. If a mmap failure aborts us here, the swap
        //    state is still whole, so recovery remains unambiguous.
        //    Derive each chunk id either from pstore's tail (already
        //    returned by a prior partial run) or from sstore (not yet
        //    returned).
        for (uint32_t k = 0; k < returning_chunks; k++) {
            uint32_t chunk_id =
                pstore.cnv_chunks[primary_old_chunks + k].cnv_chunk_id;
            if (chunk_id == detail::db_metadata::NULL_CHUNK) {
                chunk_id = sstore.cnv_chunks[k].cnv_chunk_id;
            }
            MONAD_ASSERT(chunk_id != detail::db_metadata::NULL_CHUNK);
            install_chunk_mapping_(
                *io_,
                primary_span,
                primary_old_chunks + k,
                chunk_id,
                map_bytes_per_chunk_(),
                prot_,
                mapflags_,
                can_write_to_map_,
                /*second_copy=*/which == 1);
        }
        // 2. Move chunks from secondary's list to primary's tail.
        //    Idempotent: skip if destination already holds a valid id.
        for (uint32_t k = 0; k < returning_chunks; k++) {
            if (pstore.cnv_chunks[primary_old_chunks + k].cnv_chunk_id !=
                detail::db_metadata::NULL_CHUNK) {
                continue;
            }
            auto const moved_id = sstore.cnv_chunks[k].cnv_chunk_id;
            MONAD_ASSERT(moved_id != detail::db_metadata::NULL_CHUNK);
            pstore.cnv_chunks[primary_old_chunks + k].high_bits_all_set =
                uint32_t(-1);
            pstore.cnv_chunks[primary_old_chunks + k].cnv_chunk_id = moved_id;
            sstore.cnv_chunks[k].cnv_chunk_id = detail::db_metadata::NULL_CHUNK;
        }
        // 3. Initialise the freshly-added tail positions on primary to
        //    INVALID_OFFSET, then copy any valid entries into their new
        //    positions under the grown capacity. The copy is idempotent
        //    (sources in [0, old_cap), destinations in [old_cap, new_cap),
        //    ranges disjoint, sources not written). The memset is safe to
        //    re-run during replay for the same reason as activate's step
        //    5: replay runs in the constructor before any client can
        //    observe the DB, and live-path deactivate is synchronous, so
        //    no push can have touched the tail positions we're clearing.
        if (cur_primary_chunks == primary_old_chunks && returning_chunks > 0) {
            auto const tail_bytes =
                uint64_t(returning_chunks) * map_bytes_per_chunk_();
            memset(
                (void *)(reinterpret_cast<std::byte *>(primary_span.data()) +
                         old_cap * sizeof(chunk_offset_t)),
                0xff,
                tail_bytes);
            uint64_t const nv =
                start_lifetime_as<std::atomic_uint64_t const>(pver_nv)->load(
                    std::memory_order_acquire);
            uint64_t const lb =
                start_lifetime_as<std::atomic_uint64_t const>(pver_lb)->load(
                    std::memory_order_acquire);
            if (nv != lb) {
                for (uint64_t v = lb; v < nv; v++) {
                    uint64_t const old_pos = v & (old_cap - 1);
                    uint64_t const new_pos = v & (new_cap - 1);
                    if (old_pos == new_pos) {
                        continue;
                    }
                    auto *src = start_lifetime_as<std::atomic<chunk_offset_t>>(
                        &primary_span[old_pos]);
                    auto *dst = start_lifetime_as<std::atomic<chunk_offset_t>>(
                        &primary_span[new_pos]);
                    dst->store(
                        src->load(std::memory_order_acquire),
                        std::memory_order_release);
                }
            }
        }
        // 4. Commit the grow / shrink (primary grows, secondary shrinks
        //    to 0). Idempotent stores.
        start_lifetime_as<std::atomic<uint32_t>>(&pstore.cnv_chunks_len)
            ->store(primary_new_chunks, std::memory_order_release);
        start_lifetime_as<std::atomic<uint32_t>>(&sstore.cnv_chunks_len)
            ->store(0, std::memory_order_release);
        // 5. Mark secondary inactive (idempotent).
        start_lifetime_as<std::atomic<uint8_t>>(&m->secondary_timeline_active_)
            ->store(0, std::memory_order_release);
    }
}

void DbMetadataContext::deactivate_secondary_header()
{
    MONAD_ASSERT(timeline_active(timeline_id::secondary));
    MONAD_ASSERT(
        copies_[0].main->pending_shrink_grow.op_kind ==
            detail::db_metadata::PENDING_OP_NONE &&
        copies_[1].main->pending_shrink_grow.op_kind ==
            detail::db_metadata::PENDING_OP_NONE);

    uint8_t const primary_idx = primary_ring_idx();
    uint8_t const secondary_idx = primary_idx ^ 1u;

    auto const &primary_storage =
        (primary_idx == 0) ? copies_[0].main->root_offsets.storage_
                           : copies_[0].main->secondary_timeline.storage_;
    auto const &secondary_storage =
        (secondary_idx == 0) ? copies_[0].main->root_offsets.storage_
                             : copies_[0].main->secondary_timeline.storage_;
    uint32_t const primary_old_chunks = primary_storage.cnv_chunks_len;
    uint32_t const returning_chunks = secondary_storage.cnv_chunks_len;
    MONAD_ASSERT(
        returning_chunks > 0 && primary_old_chunks > 0,
        "deactivate_secondary_header needs both rings to hold at least one "
        "chunk");
    uint32_t const primary_new_chunks = primary_old_chunks + returning_chunks;
    MONAD_ASSERT(
        (primary_new_chunks & (primary_new_chunks - 1)) == 0,
        "Grown primary ring size must remain a power of two");

    set_pending_shrink_grow_(
        detail::db_metadata::PENDING_OP_DEACTIVATE, primary_new_chunks);
    sync_metadata_to_disk_();

    do_deactivate_secondary_body_(primary_new_chunks);

    sync_ring_data_to_disk_();
    sync_metadata_to_disk_();

    clear_pending_shrink_grow_();
    sync_metadata_to_disk_();

    LOG_INFO(
        "Deactivated secondary timeline (primary ring grew from {} to {} "
        "chunks)",
        primary_old_chunks,
        primary_new_chunks);
}

void DbMetadataContext::do_promote_secondary_to_primary_body_(
    uint8_t const target_ring_idx)
{
    for (auto const &copy : copies_) {
        auto *const m = copy.main;
        auto const g = m->hold_dirty();
        start_lifetime_as<std::atomic<uint8_t>>(&m->primary_ring_idx)
            ->store(target_ring_idx, std::memory_order_release);
    }
}

void DbMetadataContext::promote_secondary_to_primary_header()
{
    MONAD_ASSERT(timeline_active(timeline_id::secondary));
    MONAD_ASSERT(
        copies_[0].main->pending_shrink_grow.op_kind ==
            detail::db_metadata::PENDING_OP_NONE &&
        copies_[1].main->pending_shrink_grow.op_kind ==
            detail::db_metadata::PENDING_OP_NONE);

    // The flip advances both metadata copies at once, so the one-clean-copy
    // dirty-bit recovery cannot heal a mid-flip crash. Use the intent log:
    // record the absolute target ring idx, make it durable, run the
    // idempotent body, then clear. A crash anywhere below leaves a non-NONE
    // op_kind that the constructor replays to completion.
    uint8_t const target_ring_idx =
        static_cast<uint8_t>(primary_ring_idx() ^ 1u);

    set_pending_shrink_grow_(
        detail::db_metadata::PENDING_OP_PROMOTE, target_ring_idx);
    sync_metadata_to_disk_();

    do_promote_secondary_to_primary_body_(target_ring_idx);
    sync_metadata_to_disk_();

    clear_pending_shrink_grow_();
    sync_metadata_to_disk_();
}

DbMetadataContext::~DbMetadataContext()
{
    for (auto &copy : copies_) {
        if (copy.ring_a_span.data() != nullptr) {
            (void)::munmap(
                copy.ring_a_span.data(), copy.ring_a_span.size_bytes());
            copy.ring_a_span = {};
        }
        if (copy.ring_b_span.data() != nullptr) {
            (void)::munmap(
                copy.ring_b_span.data(), copy.ring_b_span.size_bytes());
            copy.ring_b_span = {};
        }
    }
    // munmap db_metadata
    if (copies_[0].main != nullptr) {
        (void)::munmap(copies_[0].main, metadata_mmap_size_);
        copies_[0].main = nullptr;
    }
    if (copies_[1].main != nullptr) {
        (void)::munmap(copies_[1].main, metadata_mmap_size_);
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
    set_auto_expire_version_metadata(timeline_id::primary, 0);
    set_auto_expire_version_metadata(timeline_id::secondary, 0);

    // Zero the padding so any future field carved from it sees a
    // consistent initial value on both fresh pools and pools migrated
    // from earlier on-disk formats (the MONAD007->008 migration also
    // zeros this region).
    for (auto const i : {0, 1}) {
        auto *const m = copies_[i].main;
        auto const g = m->hold_dirty();
        memset(
            m->future_variables_unused, 0, sizeof(m->future_variables_unused));
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

    map_ring_a_storage();
    map_ring_b_storage();
    // New pool: primary_ring_idx defaults to 0 (ring_a primary) and
    // secondary_timeline_active_ = 0 (inactive) from the initial zeroing.
    // Ring_b has no chunks yet (cnv_chunks_len == 0); activate_secondary
    // will allocate chunks to it, map them, and fill with INVALID_OFFSET.
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
