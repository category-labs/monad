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
#include <category/mpt/util.hpp>

#include <atomic>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>

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
    struct metadata_copy
    {
        detail::db_metadata *main{nullptr};
        std::span<chunk_offset_t> root_offsets;
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

    auto root_offsets(unsigned const which = 0) const
    {
        class root_offsets_delegator
        {
            std::atomic_ref<uint64_t> version_lower_bound_;
            std::atomic_ref<uint64_t> next_version_;
            std::span<chunk_offset_t> root_offsets_chunks_;

            void
            update_version_lower_bound_(uint64_t lower_bound = uint64_t(-1))
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
            explicit root_offsets_delegator(metadata_copy const *m)
                : version_lower_bound_(
                      m->main->root_offsets.version_lower_bound_)
                , next_version_(m->main->root_offsets.next_version_)
                , root_offsets_chunks_(
                      std::span<chunk_offset_t>(m->root_offsets))
            {
                MONAD_ASSERT_PRINTF(
                    root_offsets_chunks_.size() ==
                        1ULL
                            << (63 -
                                std::countl_zero(root_offsets_chunks_.size())),
                    "root offsets chunks size is %lu, not a power of 2",
                    root_offsets_chunks_.size());
            }

            size_t capacity() const noexcept
            {
                return root_offsets_chunks_.size();
            }

            void push(chunk_offset_t const o) noexcept
            {
                auto const wp = next_version_.load(std::memory_order_relaxed);
                auto const next_wp = wp + 1;
                MONAD_ASSERT(next_wp != 0);
                auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &root_offsets_chunks_
                        [wp & (root_offsets_chunks_.size() - 1)]);
                p->store(o, std::memory_order_release);
                next_version_.store(next_wp, std::memory_order_release);
                if (o != INVALID_OFFSET) {
                    update_version_lower_bound_();
                }
            }

            void assign(size_t const i, chunk_offset_t const o) noexcept
            {
                auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &root_offsets_chunks_
                        [i & (root_offsets_chunks_.size() - 1)]);
                p->store(o, std::memory_order_release);
                update_version_lower_bound_(
                    (o != INVALID_OFFSET) ? i : uint64_t(-1));
            }

            chunk_offset_t operator[](size_t const i) const noexcept
            {
                return start_lifetime_as<std::atomic<chunk_offset_t> const>(
                           &root_offsets_chunks_
                               [i & (root_offsets_chunks_.size() - 1)])
                    ->load(std::memory_order_acquire);
            }

            // return INVALID_BLOCK_NUM indicates that db is empty
            uint64_t max_version() const noexcept
            {
                auto const wp = next_version_.load(std::memory_order_acquire);
                return wp - 1;
            }

            void reset_all(uint64_t const version)
            {
                version_lower_bound_.store(0, std::memory_order_release);
                next_version_.store(0, std::memory_order_release);
                memset(
                    (void *)root_offsets_chunks_.data(),
                    0xff,
                    root_offsets_chunks_.size() * sizeof(chunk_offset_t));
                version_lower_bound_.store(version, std::memory_order_release);
                next_version_.store(version, std::memory_order_release);
            }

            void rewind_to_version(uint64_t const version)
            {
                MONAD_ASSERT(version < max_version());
                MONAD_ASSERT(max_version() - version <= capacity());
                for (uint64_t i = version + 1; i <= max_version(); i++) {
                    assign(i, async::INVALID_OFFSET);
                }
                if (version <
                    version_lower_bound_.load(std::memory_order_acquire)) {
                    version_lower_bound_.store(
                        version, std::memory_order_release);
                }
                next_version_.store(version + 1, std::memory_order_release);
                update_version_lower_bound_();
            }
        };

        return root_offsets_delegator{&copies_[which]};
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
    int64_t get_auto_expire_version_metadata() const noexcept;
    void set_auto_expire_version_metadata(int64_t version) noexcept;
    void update_history_length_metadata(uint64_t history_len) noexcept;

    // Root offsets operations
    void append_root_offset(chunk_offset_t root_offset) noexcept;
    void update_root_offset(size_t i, chunk_offset_t root_offset) noexcept;
    void fast_forward_next_version(uint64_t version) noexcept;
    void clear_root_offsets_up_to_and_including(uint64_t version);

    // DB offsets
    void advance_db_offsets_to(
        chunk_offset_t fast_offset, chunk_offset_t slow_offset) noexcept;

    // History/version queries
    uint64_t version_history_max_possible() const noexcept;
    uint64_t version_history_length() const noexcept;
    uint64_t db_history_min_valid_version() const noexcept;
    uint64_t db_history_max_version() const noexcept;
    uint64_t db_history_range_lower_bound() const noexcept;

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

    chunk_offset_t get_root_offset_at_version(uint64_t version) const noexcept;

    bool version_is_valid_ondisk(uint64_t version) const noexcept
    {
        return get_root_offset_at_version(version) != INVALID_OFFSET;
    }

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
    // Map root_offsets from cnv chunks. Called by the constructor for existing
    // pools, and by UpdateAux::init() after writing magic for new pools.
    void map_root_offsets();

    detail::db_metadata *main_mutable(unsigned const which = 0) noexcept
    {
        return copies_[which].main;
    }

    MONAD_ASYNC_NAMESPACE::AsyncIO *io_{nullptr};
    metadata_copy copies_[2];
    size_t db_map_size_{0};
    bool is_new_pool_{false};
    bool can_write_to_map_{false};
    int prot_{0};
    int mapflags_{0};
};

MONAD_MPT_NAMESPACE_END
