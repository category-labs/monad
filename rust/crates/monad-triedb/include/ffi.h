// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <cstddef>
#include <cstdint>
#include <memory>

#include "rust/cxx.h"

#include <category/execution/monad/staking/read_valset.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/state_machine.hpp>

namespace monad::rust
{
    struct UpsertEntry;
    struct Context;

    struct TriedbRoInner
    {
        monad::mpt::AsyncIOContext io_ctx;
        monad::mpt::Db db;
        monad::mpt::AsyncContext async_ctx;

        TriedbRoInner(
            monad::mpt::ReadOnlyOnDiskDbConfig const &config,
            uint64_t const node_lru_max_mem)
            : io_ctx(config)
            , db(io_ctx)
            , async_ctx(db, node_lru_max_mem)
        {
        }
    };

    struct TriedbRwInner
    {
        // Must outlive `db`.
        std::unique_ptr<monad::mpt::StateMachine> state_machine;
        monad::mpt::Db db;
        std::shared_ptr<monad::mpt::Node> root;

        TriedbRwInner(
            std::unique_ptr<monad::mpt::StateMachine> sm,
            monad::mpt::OnDiskDbConfig const &config)
            : state_machine(std::move(sm))
            , db(*state_machine, config)
            , root()
        {
        }
    };

    std::unique_ptr<TriedbRoInner> triedb_open(
        ::rust::Str dbdirpath, uint64_t node_lru_max_mem,
        bool disable_mismatching_storage_pool_check);

    std::unique_ptr<TriedbRwInner> triedb_open_rw_memory(
        uint64_t node_lru_max_mem, int64_t file_size_gb, bool compaction);

    /// `append = true` preserves existing data; `append = false` truncates.
    std::unique_ptr<TriedbRwInner> triedb_open_rw(
        ::rust::Str dbdirpath, bool append, uint64_t node_lru_max_mem,
        int64_t file_size_gb, bool compaction);

    inline size_t
    triedb_poll(TriedbRoInner &inner, bool const blocking, size_t const count)
    {
        return inner.db.poll(blocking, count);
    }

#define MONAD_RUST_METADATA_GETTER(name, ret, call)                            \
    inline ret triedb_##name(TriedbRoInner const &inner)                       \
    {                                                                          \
        return inner.db.call();                                                \
    }                                                                          \
    inline ret triedb_##name(TriedbRwInner const &inner)                       \
    {                                                                          \
        return inner.db.call();                                                \
    }

    MONAD_RUST_METADATA_GETTER(
        latest_proposed_version, uint64_t, get_latest_proposed_version)
    MONAD_RUST_METADATA_GETTER(
        latest_voted_version, uint64_t, get_latest_voted_version)
    MONAD_RUST_METADATA_GETTER(
        latest_finalized_version, uint64_t, get_latest_finalized_version)
    MONAD_RUST_METADATA_GETTER(
        latest_verified_version, uint64_t, get_latest_verified_version)
    MONAD_RUST_METADATA_GETTER(earliest_version, uint64_t, get_earliest_version)
    MONAD_RUST_METADATA_GETTER(latest_version, uint64_t, get_latest_version)
    MONAD_RUST_METADATA_GETTER(
        latest_proposed_block_id, monad::bytes32_t,
        get_latest_proposed_block_id)
    MONAD_RUST_METADATA_GETTER(
        latest_voted_block_id, monad::bytes32_t, get_latest_voted_block_id)

#undef MONAD_RUST_METADATA_GETTER

    namespace detail
    {
        inline std::unique_ptr<monad::mpt::NodeCursor> triedb_find_common(
            monad::mpt::Db const &db, ::rust::Slice<uint8_t const> const key,
            uint8_t const key_len_nibbles, uint64_t const block_id)
        {
            auto result = db.find(
                monad::mpt::NibblesView{
                    0u, static_cast<unsigned>(key_len_nibbles), key.data()},
                block_id);
            if (!result.has_value()) {
                return nullptr;
            }
            return std::make_unique<monad::mpt::NodeCursor>(
                std::move(result.value()));
        }
    }

    /// Returns null if the key is absent. The returned cursor pins the
    /// node (and thus its value bytes) in the node cache until dropped.
    inline std::unique_ptr<monad::mpt::NodeCursor> triedb_find(
        TriedbRoInner const &inner, ::rust::Slice<uint8_t const> const key,
        uint8_t const key_len_nibbles, uint64_t const block_id)
    {
        return detail::triedb_find_common(
            inner.db, key, key_len_nibbles, block_id);
    }

    inline std::unique_ptr<monad::mpt::NodeCursor> triedb_find(
        TriedbRwInner const &inner, ::rust::Slice<uint8_t const> const key,
        uint8_t const key_len_nibbles, uint64_t const block_id)
    {
        return detail::triedb_find_common(
            inner.db, key, key_len_nibbles, block_id);
    }

    /// Returns a view into the node's internal storage. Valid only while
    /// `cursor` is alive.
    ::rust::Slice<uint8_t const>
    node_cursor_value(monad::mpt::NodeCursor const &cursor);

    void triedb_async_read(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> key,
        uint8_t key_len_nibbles, uint64_t block_id, Context *ctx);

    bool triedb_traverse_sync(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> key,
        uint8_t key_len_nibbles, uint64_t block_id, Context *ctx);

    void triedb_async_traverse(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> key,
        uint8_t key_len_nibbles, uint64_t block_id, Context *ctx);

    void triedb_async_ranged_get(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> prefix_key,
        uint8_t prefix_key_len_nibbles, ::rust::Slice<uint8_t const> min_key,
        uint8_t min_key_len_nibbles, ::rust::Slice<uint8_t const> max_key,
        uint8_t max_key_len_nibbles, uint64_t block_id, Context *ctx);

    ::rust::Vec<monad::staking::Validator> triedb_read_valset(
        TriedbRoInner &inner, size_t block_num, uint64_t requested_epoch,
        bool &found);

    void triedb_upsert(
        TriedbRwInner &inner, ::rust::Slice<UpsertEntry const> const updates,
        uint64_t block_id);

    void triedb_clear_root(TriedbRwInner &inner);

    /// Returns `false` if no such version exists on disk.
    bool triedb_load_root(TriedbRwInner &inner, uint64_t version);

    void
    triedb_update_finalized_version(TriedbRwInner &inner, uint64_t version);

    void triedb_update_voted_metadata(
        TriedbRwInner &inner, uint64_t version,
        monad::bytes32_t const &block_id);

    void triedb_update_proposed_metadata(
        TriedbRwInner &inner, uint64_t version,
        monad::bytes32_t const &block_id);
}
