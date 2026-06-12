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
#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/util.hpp>

#include <atomic>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <sys/mman.h>

MONAD_MPT_NAMESPACE_BEGIN

// Owns mmap'd metadata regions for a single DB within a storage pool.
// Handles the storage-level lifecycle: mmap, dirty recovery, magic validation,
// new pool initialization of metadata and root_offsets storage, and munmap.
//
// Separated from UpdateAux so that the metadata mmap lifecycle can be
// managed independently (e.g. by a pool-level owner in multi-DB setups).
class DbMetadataContext
{
    friend class UpdateAux;

public:
    // Each metadata_copy describes one of the two redundant db_metadata
    // instances. `ring_a_span` / `ring_b_span` are in-memory spans over the
    // physical storage of ring_a (cnv chunks listed in
    // db_metadata::root_offsets.storage_.cnv_chunks[]) and ring_b (cnv
    // chunks listed in the secondary timeline's storage_.cnv_chunks). These
    // spans are tied to physical rings, not timeline roles — role routing
    // happens at query time via db_metadata::primary_ring_idx.
    struct metadata_copy
    {
        detail::db_metadata *main{nullptr};
        std::span<chunk_offset_t> ring_a_span;
        std::span<chunk_offset_t> ring_b_span;
    };

    // Ring delegator for the root-offsets ring buffer. Bound to the
    // header/span of one physical ring plus a snapshot of its current
    // capacity (entries, not chunks). Capacity changes only via the
    // offline-only activate_secondary_header / deactivate_secondary_header,
    // so the snapshot is stable for any concurrent reader.
    class root_offsets_delegator
    {
        std::atomic_ref<uint64_t> version_lower_bound_;
        std::atomic_ref<uint64_t> next_version_;
        std::span<chunk_offset_t> root_offsets_chunks_;
        size_t capacity_; // entries in the *live* portion of the ring

        void update_version_lower_bound_(uint64_t lower_bound = uint64_t(-1))
        {
            auto const version_lower_bound =
                version_lower_bound_.load(std::memory_order_acquire);
            auto idx = (lower_bound < version_lower_bound)
                           ? lower_bound
                           : version_lower_bound;
            auto const max_version =
                next_version_.load(std::memory_order_acquire) - 1;
            if (max_version == INVALID_BLOCK_NUM) {
                return;
            }
            while (idx < max_version && (*this)[idx] == INVALID_OFFSET) {
                idx++;
            }
            if (idx != version_lower_bound) {
                version_lower_bound_.store(idx, std::memory_order_release);
            }
        }

    public:
        root_offsets_delegator(
            uint64_t &version_lower_bound, uint64_t &next_version,
            std::span<chunk_offset_t> root_offsets_chunks,
            size_t const capacity)
            : version_lower_bound_(version_lower_bound)
            , next_version_(next_version)
            , root_offsets_chunks_(root_offsets_chunks)
            , capacity_(capacity)
        {
            MONAD_ASSERT(capacity_ <= root_offsets_chunks_.size());
            MONAD_ASSERT_PRINTF(
                capacity_ == 0 ||
                    capacity_ == 1ULL << (63 - std::countl_zero(capacity_)),
                "root offsets capacity %lu is not a power of 2",
                capacity_);
        }

        bool empty() const noexcept
        {
            return capacity_ == 0;
        }

        size_t capacity() const noexcept
        {
            return capacity_;
        }

        void push(chunk_offset_t const o) noexcept
        {
            MONAD_ASSERT(capacity_ != 0);
            auto const wp = next_version_.load(std::memory_order_relaxed);
            auto const next_wp = wp + 1;
            MONAD_ASSERT(next_wp != 0);
            auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                &root_offsets_chunks_[wp & (capacity_ - 1)]);
            p->store(o, std::memory_order_release);
            next_version_.store(next_wp, std::memory_order_release);
            if (o != INVALID_OFFSET) {
                update_version_lower_bound_();
            }
        }

        void assign(size_t const i, chunk_offset_t const o) noexcept
        {
            MONAD_ASSERT(capacity_ != 0);
            auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                &root_offsets_chunks_[i & (capacity_ - 1)]);
            p->store(o, std::memory_order_release);
            update_version_lower_bound_(
                (o != INVALID_OFFSET) ? i : uint64_t(-1));
        }

        chunk_offset_t operator[](size_t const i) const noexcept
        {
            MONAD_ASSERT(capacity_ != 0);
            return start_lifetime_as<std::atomic<chunk_offset_t> const>(
                       &root_offsets_chunks_[i & (capacity_ - 1)])
                ->load(std::memory_order_acquire);
        }

        // return INVALID_BLOCK_NUM indicates that db is empty
        uint64_t max_version() const noexcept
        {
            auto const wp = next_version_.load(std::memory_order_acquire);
            return wp - 1;
        }

        uint64_t version_lower_bound() const noexcept
        {
            return version_lower_bound_.load(std::memory_order_acquire);
        }

        void reset_all(uint64_t const version)
        {
            MONAD_ASSERT(capacity_ != 0);
            version_lower_bound_.store(0, std::memory_order_release);
            next_version_.store(0, std::memory_order_release);
            memset(
                (void *)root_offsets_chunks_.data(),
                0xff,
                capacity_ * sizeof(chunk_offset_t));
            version_lower_bound_.store(version, std::memory_order_release);
            next_version_.store(version, std::memory_order_release);
        }

        void rewind_to_version(uint64_t const version)
        {
            MONAD_ASSERT(version < max_version());
            MONAD_ASSERT(max_version() - version <= capacity_);
            for (uint64_t i = version + 1; i <= max_version(); i++) {
                assign(i, async::INVALID_OFFSET);
            }
            if (version <
                version_lower_bound_.load(std::memory_order_acquire)) {
                version_lower_bound_.store(version, std::memory_order_release);
            }
            next_version_.store(version + 1, std::memory_order_release);
            update_version_lower_bound_();
        }
    };

    // Construct and mmap metadata from the given AsyncIO's storage pool.
    explicit DbMetadataContext(MONAD_ASYNC_NAMESPACE::AsyncIO &io);

    ~DbMetadataContext();

    DbMetadataContext(DbMetadataContext const &) = delete;
    DbMetadataContext &operator=(DbMetadataContext const &) = delete;
    DbMetadataContext(DbMetadataContext &&) = delete;
    DbMetadataContext &operator=(DbMetadataContext &&) = delete;

    detail::db_metadata const *main(unsigned const which = 0) const noexcept
    {
        return copies_[which].main;
    }

    bool is_new_pool() const noexcept
    {
        return is_new_pool_;
    }

    //! \brief Force both metadata copies to durable storage. Public entry
    //! point for monad-mpt --upgrade's post-migration flush. Requires the
    //! pool to have been opened writable (asserts can_write_to_map_).
    void sync_metadata_to_disk();

    enum class chunk_list : uint8_t
    {
        free = 0,
        fast = 1,
        slow = 2
    };

    void append(chunk_list list, uint32_t idx);
    void remove(uint32_t idx) noexcept;

    // Initialize a brand new pool: chunk lists, version markers, magic,
    // root_offsets mapping, and optionally history length.
    // initial_insertion_count is for unit testing only (normally 0).
    void init_new_pool(
        std::optional<uint64_t> history_len = {},
        uint32_t initial_insertion_count = 0);

    // Which physical ring is currently the logical primary. 0 = ring_a,
    // 1 = ring_b. Atomic acquire load so callers that branch on it pair
    // naturally with a promote flip done under release.
    uint8_t primary_ring_idx() const noexcept
    {
        return start_lifetime_as<std::atomic<uint8_t> const>(
                   &copies_[0].main->primary_ring_idx)
            ->load(std::memory_order_acquire);
    }

    root_offsets_delegator
    root_offsets(timeline_id const tid, unsigned const which = 0) const
    {
        auto const primary_idx = primary_ring_idx();
        auto const ring_idx = (tid == timeline_id::primary)
                                  ? primary_idx
                                  : static_cast<uint8_t>(primary_idx ^ 1u);
        return ring_delegator_(ring_idx, which);
    }

    root_offsets_delegator root_offsets(unsigned const which = 0) const
    {
        return root_offsets(timeline_id::primary, which);
    }

    // Version metadata getters/setters
    uint64_t get_latest_finalized_version() const noexcept;
    void set_latest_finalized_version(uint64_t version) noexcept;
    uint64_t get_latest_verified_version() const noexcept;
    void set_latest_verified_version(uint64_t version) noexcept;
    uint64_t get_latest_voted_version() const noexcept;
    bytes32_t get_latest_voted_block_id() const noexcept;
    void set_latest_voted(uint64_t version, bytes32_t const &block_id) noexcept;
    uint64_t get_latest_proposed_version() const noexcept;
    bytes32_t get_latest_proposed_block_id() const noexcept;
    void
    set_latest_proposed(uint64_t version, bytes32_t const &block_id) noexcept;
    int64_t get_auto_expire_version_metadata(timeline_id tid) const noexcept;
    void
    set_auto_expire_version_metadata(timeline_id tid, int64_t version) noexcept;

    // Read the persisted StateMachine kind for the given timeline. Stamped
    // at pool create time by monad-mpt --state-machine and on
    // activate-secondary for the non-primary ring; consumed by mpt::Db's
    // production-open ctor to pick the right SM via the registry in
    // state_machine_kind.hpp.
    state_machine_kind get_state_machine_kind(timeline_id tid) const noexcept;
    void
    set_state_machine_kind(timeline_id tid, state_machine_kind kind) noexcept;
    void update_history_length_metadata(uint64_t history_len) noexcept;

    // Root offsets operations. All wrap the two-copy mutation in
    // per-copy hold_dirty() scopes so crash recovery can roll back a
    // half-written update. tid selects which ring to mutate.
    void
    append_root_offset(chunk_offset_t root_offset, timeline_id tid) noexcept;
    void update_root_offset(
        size_t i, chunk_offset_t root_offset, timeline_id tid) noexcept;
    void fast_forward_next_version(uint64_t version, timeline_id tid) noexcept;

    // DB offsets
    void advance_db_offsets_to(
        chunk_offset_t fast_offset, chunk_offset_t slow_offset) noexcept;

    // History/version queries
    uint64_t version_history_max_possible() const noexcept;
    uint64_t version_history_length() const noexcept;
    uint64_t db_history_min_valid_version() const noexcept;
    uint64_t db_history_max_version() const noexcept;
    uint64_t db_history_range_lower_bound() const noexcept;
    uint64_t db_history_range_lower_bound(timeline_id tid) const noexcept;

    // Inline accessors
    chunk_offset_t get_start_of_wip_fast_offset() const noexcept
    {
        return copies_[0].main->db_offsets.start_of_wip_offset_fast;
    }

    chunk_offset_t get_start_of_wip_slow_offset() const noexcept
    {
        return copies_[0].main->db_offsets.start_of_wip_offset_slow;
    }

    file_offset_t get_lower_bound_free_space() const noexcept
    {
        return copies_[0].main->capacity_in_free_list;
    }

    chunk_offset_t get_latest_root_offset() const noexcept
    {
        auto const ro = root_offsets();
        return ro[ro.max_version()];
    }

    // Timeline-aware queries. The single-arg overloads delegate to these
    // with timeline_id::primary. For timeline_id::secondary they return
    // INVALID / INVALID_BLOCK_NUM when the timeline is inactive, so
    // callers don't need to guard with timeline_active() separately.
    bool timeline_active(timeline_id tid) const noexcept;
    chunk_offset_t get_root_offset_at_version(
        uint64_t version, timeline_id tid) const noexcept;

    bool
    version_is_valid_ondisk(uint64_t version, timeline_id tid) const noexcept
    {
        return get_root_offset_at_version(version, tid) != INVALID_OFFSET;
    }

    uint64_t db_history_max_version(timeline_id tid) const noexcept;
    uint64_t db_history_min_valid_version(timeline_id tid) const noexcept;

    chunk_offset_t get_root_offset_at_version(uint64_t version) const noexcept;

    bool version_is_valid_ondisk(uint64_t const version) const noexcept
    {
        return version_is_valid_ondisk(version, timeline_id::primary);
    }

    // Secondary timeline lifecycle (metadata only; UpdateAux pairs these
    // with per-timeline compaction state updates).
    //
    // activate_secondary_header shrinks the primary ring to half its
    // chunks, mmaps the freed chunks into the non-primary ring, and flips
    // secondary_timeline_active_. The new ring's header stays at INVALID
    // defaults until its first upsert seeds it. deactivate_secondary_header
    // is the reverse. Offline-only: no reader may be attached while these
    // run (enforced outside the DB), so no reader-side synchronisation is
    // needed.
    void activate_secondary_header();
    void deactivate_secondary_header();

    // Flips primary_ring_idx on both metadata copies, swapping which
    // physical ring is the logical primary. Persistent across restart
    // because the byte is on-disk metadata; map_ring_a_storage /
    // map_ring_b_storage always map their physical rings from fixed
    // locations, and role routing in root_offsets(timeline_id) reads the
    // byte at query time. The flip touches both metadata copies, so it
    // cannot rely on the one-clean-copy dirty-bit recovery; it is made
    // crash-safe by the pending_shrink_grow intent log + idempotent replay,
    // the same mechanism activate/deactivate use.
    void promote_secondary_to_primary_header();

    // Apply a function to both metadata copies
    template <typename Func, typename... Args>
        requires std::invocable<
            std::function<void(detail::db_metadata *, Args...)>,
            detail::db_metadata *, Args...>
    void modify_metadata(Func func, Args const &...args) noexcept
    {
        func(copies_[0].main, args...);
        func(copies_[1].main, args...);
    }

private:
    // Map ring storage from cnv chunks. Called by the constructor for
    // existing pools, and by init_new_pool after writing magic for new
    // pools. Each reserves a max-sized virtual address range sized for
    // `ring_max_chunks_()`; currently-present chunks (per
    // root_offsets/secondary_timeline.storage_.cnv_chunks[]) are MAP_FIXED
    // into their slots. Unoccupied tail slots remain anonymous PROT_NONE
    // until a future grow maps a chunk into them. Pre-reservation keeps
    // the span pointer stable across shrink/grow.
    void map_ring_a_storage();
    void map_ring_b_storage();

    // Shared helper for the two map_* functions above. The `span_field`
    // member pointer selects which span slot on metadata_copy gets the
    // reservation pointer. Defined in the header because Storage is the
    // unnameable anonymous nested type inside root_offsets_ring_t.
    template <typename Storage>
    void map_ring_storage_(
        Storage const &storage,
        std::span<chunk_offset_t> metadata_copy::*span_field,
        char const *const ring_name)
    {
        auto const max_chunks = ring_max_chunks_();
        MONAD_ASSERT_PRINTF(
            storage.cnv_chunks_len <= max_chunks,
            "%s requires %u conventional chunk(s) but the storage pool "
            "provides only %u for ring data; the pool was created with fewer "
            "conventional chunks than this DB needs",
            ring_name,
            storage.cnv_chunks_len,
            max_chunks);
        auto const map_bytes = map_bytes_per_chunk_();
        auto const reservation_bytes = max_chunks * map_bytes;
        auto const entries_per_chunk = map_bytes / sizeof(chunk_offset_t);

        std::byte *reservation[2];
        for (auto &r : reservation) {
            r = (std::byte *)::mmap(
                nullptr,
                reservation_bytes,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
                -1,
                0);
            MONAD_ASSERT(r != MAP_FAILED);
        }

        for (size_t n = 0; n < storage.cnv_chunks_len; n++) {
            auto const cnv_chunk_id = storage.cnv_chunks[n].cnv_chunk_id;
            // Tolerate partial-move state: a crash during the cnv_chunks[]
            // swap in activate/deactivate can leave a slot at NULL_CHUNK
            // while cnv_chunks_len still includes it. The tail VA is
            // PROT_NONE from the initial reservation; leave it alone and
            // let replay_pending_shrink_grow_ install the correct mapping
            // after reconstructing the swap.
            if (cnv_chunk_id == detail::db_metadata::NULL_CHUNK) {
                continue;
            }
            auto &chunk = io_->storage_pool().chunk(
                MONAD_ASYNC_NAMESPACE::storage_pool::cnv, cnv_chunk_id);
            auto const fdr = chunk.read_fd();
            auto const fdw = chunk.write_fd(0);
            auto const &fd = can_write_to_map_ ? fdw : fdr;
            MONAD_ASSERT(
                MAP_FAILED != ::mmap(
                                  reservation[0] + n * map_bytes,
                                  map_bytes,
                                  prot_,
                                  mapflags_ | MAP_FIXED,
                                  fd.first,
                                  off_t(fdr.second)));
            MONAD_ASSERT(
                MAP_FAILED != ::mmap(
                                  reservation[1] + n * map_bytes,
                                  map_bytes,
                                  prot_,
                                  mapflags_ | MAP_FIXED,
                                  fd.first,
                                  off_t(fdr.second + map_bytes)));
        }

        copies_[0].*span_field = {
            start_lifetime_as<chunk_offset_t>((chunk_offset_t *)reservation[0]),
            max_chunks * entries_per_chunk};
        copies_[1].*span_field = {
            start_lifetime_as<chunk_offset_t>((chunk_offset_t *)reservation[1]),
            max_chunks * entries_per_chunk};
    }

    // MAX chunks any single ring could hold = total cnv chunks - 1 (the
    // first cnv chunk stores db_metadata). Computed from the storage pool
    // at call time; constant for the life of the pool.
    uint32_t ring_max_chunks_() const noexcept;

    // Virtual address range size per cnv chunk, i.e. half a cnv chunk's
    // capacity (the other half holds the second metadata copy's ring
    // data). Constant for the life of the pool.
    size_t map_bytes_per_chunk_() const noexcept;

    // Construct a delegator bound to physical ring `ring_idx` (0 = ring_a,
    // 1 = ring_b) on metadata copy `which`. Capacity snapshot comes from
    // the ring's cnv_chunks_len × entries_per_chunk. Capacity changes only
    // via the offline-only shrink/grow operations, so it is stable for any
    // concurrent reader.
    root_offsets_delegator
    ring_delegator_(uint8_t ring_idx, unsigned which) const
    {
        auto const *m = &copies_[which];
        auto const entries_per_chunk =
            map_bytes_per_chunk_() / sizeof(chunk_offset_t);
        if (ring_idx == 0) {
            return root_offsets_delegator{
                m->main->root_offsets.version_lower_bound_,
                m->main->root_offsets.next_version_,
                m->ring_a_span,
                start_lifetime_as<std::atomic<uint32_t> const>(
                    &m->main->root_offsets.storage_.cnv_chunks_len)
                        ->load(std::memory_order_acquire) *
                    entries_per_chunk};
        }
        return root_offsets_delegator{
            m->main->secondary_timeline.version_lower_bound_,
            m->main->secondary_timeline.next_version_,
            m->ring_b_span,
            start_lifetime_as<std::atomic<uint32_t> const>(
                &m->main->secondary_timeline.storage_.cnv_chunks_len)
                    ->load(std::memory_order_acquire) *
                entries_per_chunk};
    }

    detail::db_metadata *main_mutable(unsigned const which = 0) noexcept
    {
        return copies_[which].main;
    }

    // Force metadata chunk 0 (both copies) to durable storage. Called at
    // the start and end of every activate/deactivate_secondary_header so
    // that the pending_shrink_grow intent log state is committed to disk
    // before and after the body runs.
    void sync_metadata_to_disk_();

    // Force the currently-occupied portions of ring_a and ring_b to durable
    // storage. Called at the end of activate/deactivate body before the
    // pending flag is cleared, so that by the time the cleared flag
    // becomes durable, the ring data it describes is also durable.
    void sync_ring_data_to_disk_();

    // Stamp / clear the pending-op intent log on both metadata copies under
    // hold_dirty so the dirty-bit recovery path rolls back any mid-stamp
    // crash cleanly.
    void set_pending_shrink_grow_(
        detail::db_metadata::pending_op_kind op_kind, uint32_t op_param);
    void clear_pending_shrink_grow_();

    // Inner body of activate_secondary_header. Idempotent under replay.
    // Expects the pending flag to already be stamped.
    void do_activate_secondary_body_(uint32_t new_chunks);

    // Inner body of deactivate_secondary_header. Idempotent under replay.
    // Expects the pending flag to already be stamped.
    void do_deactivate_secondary_body_(uint32_t primary_new_chunks);

    // Inner body of promote_secondary_to_primary_header. Idempotent under
    // replay: stores the absolute target primary_ring_idx on both copies
    // (not an xor-flip, which would not converge under partial replay).
    // Expects the pending flag to already be stamped.
    void do_promote_secondary_to_primary_body_(uint8_t target_ring_idx);

    // Called from the constructor after map_ring_a/b_storage. If either
    // metadata copy has pending_shrink_grow.op_kind != NONE, replays the
    // operation to completion before the constructor returns.
    void replay_pending_shrink_grow_();

    MONAD_ASYNC_NAMESPACE::AsyncIO *io_{nullptr};
    metadata_copy copies_[2];
    // db_map_size_ is the logical bytes of live metadata (header +
    // chunk_info[]); metadata_mmap_size_ is the total VA reservation
    // (cnv chunk 0 half-capacity). The latter is always >= the former
    // and >= MONAD007_DB_METADATA_SIZE + chunk_info[], so migration
    // from a MONAD007 pool can read and relocate chunk_info[] without
    // remapping. Use metadata_mmap_size_ for mmap/munmap and
    // db_map_size_ for msync/db_copy to avoid syncing megabytes of
    // dead bytes beyond the logical metadata.
    size_t db_map_size_{0};
    size_t metadata_mmap_size_{0};
    bool is_new_pool_{false};
    bool can_write_to_map_{false};
    int prot_{0};
    int mapflags_{0};
};

MONAD_MPT_NAMESPACE_END
