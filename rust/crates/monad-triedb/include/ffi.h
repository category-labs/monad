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

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <vector>

#include "rust/cxx.h"

#include <category/execution/monad/staking/read_valset.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/state_machine.hpp>

namespace monad::mpt
{
    inline ::rust::Slice<uint8_t const>
    node_cursor_as_bytes(NodeCursor const &cursor)
    {
        auto const &val = cursor.node->value();
        return {val.data(), val.size()};
    }
} // namespace monad::mpt

namespace monad::staking
{
    inline std::array<uint8_t, 33>
    validator_secp_pubkey(Validator const &validator)
    {
        std::array<uint8_t, 33> out;
        std::copy_n(validator.secp_pubkey, out.size(), out.begin());
        return out;
    }

    inline std::array<uint8_t, 48>
    validator_bls_pubkey(Validator const &validator)
    {
        std::array<uint8_t, 48> out;
        std::copy_n(validator.bls_pubkey, out.size(), out.begin());
        return out;
    }

    inline std::array<uint8_t, 32> validator_stake(Validator const &validator)
    {
        std::array<uint8_t, 32> out;
        std::copy_n(validator.stake.bytes, out.size(), out.begin());
        return out;
    }
} // namespace monad::staking

namespace monad::rust::ffi
{
    struct CallbackContext;
} // namespace monad::rust::ffi

namespace monad::rust
{
    struct TriedbRoInner
    {
        monad::mpt::AsyncIOContext io_ctx;
        monad::mpt::Db db;
        monad::mpt::AsyncContext async_ctx;

        explicit TriedbRoInner(
            std::vector<std::filesystem::path> dbname_paths,
            uint64_t node_lru_max_mem,
            bool disable_mismatching_storage_pool_check);
    };

    struct TriedbRwInner
    {
        monad::mpt::Db db;
        std::shared_ptr<monad::mpt::Node> root;

        TriedbRwInner(
            std::unique_ptr<monad::mpt::StateMachine> sm,
            monad::mpt::OnDiskDbConfig const &config)
            : db(std::move(sm), config)
            , root()
        {
        }
    };
} // namespace monad::rust

#include "monad-triedb/src/ffi.rs.h"

namespace monad::rust
{
    std::unique_ptr<TriedbRoInner> triedb_open_ro(
        ::rust::Str dbdirpath, uint64_t node_lru_max_mem,
        bool disable_mismatching_storage_pool_check);

    std::unique_ptr<TriedbRwInner> triedb_open_rw(
        ::rust::Str dbdirpath, bool append, int64_t file_size_gb,
        bool compaction);

    std::unique_ptr<TriedbRwInner>
    triedb_open_rw_memory(int64_t file_size_gb, bool compaction);

#define MONAD_RUST_TRIEDB_METADATA_GETTER(name, ret, call)                     \
    inline ret triedb_ro_##name(TriedbRoInner const &inner)                    \
    {                                                                          \
        return inner.db.call();                                                \
    }                                                                          \
    inline ret triedb_rw_##name(TriedbRwInner const &inner)                    \
    {                                                                          \
        return inner.db.call();                                                \
    }

    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_proposed_version, uint64_t, get_latest_proposed_version)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_voted_version, uint64_t, get_latest_voted_version)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_finalized_version, uint64_t, get_latest_finalized_version)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_verified_version, uint64_t, get_latest_verified_version)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        earliest_version, uint64_t, get_earliest_version)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_version, uint64_t, get_latest_version)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_proposed_block_id, monad::bytes32_t,
        get_latest_proposed_block_id)
    MONAD_RUST_TRIEDB_METADATA_GETTER(
        latest_voted_block_id, monad::bytes32_t, get_latest_voted_block_id)

#undef MONAD_RUST_TRIEDB_METADATA_GETTER

    std::unique_ptr<monad::mpt::NodeCursor> triedb_ro_read(
        TriedbRoInner const &inner, NibblesView key, uint64_t block_id);

    std::unique_ptr<monad::mpt::NodeCursor> triedb_rw_read(
        TriedbRwInner const &inner, NibblesView key, uint64_t block_id);

    inline size_t triedb_ro_poll(
        TriedbRoInner &inner, bool const blocking, size_t const count)
    {
        return inner.db.poll(blocking, count);
    }

    void triedb_ro_async_read(
        TriedbRoInner &inner, NibblesView key, uint64_t block_id,
        ffi::CallbackContext *ctx);

    void triedb_ro_async_ranged_get(
        TriedbRoInner &inner, NibblesView prefix, NibblesView min,
        NibblesView max, uint64_t block_id, ffi::CallbackContext *ctx);

    void triedb_ro_traverse(
        TriedbRoInner &inner, NibblesView key, uint64_t block_id,
        ffi::CallbackContext *ctx);

    void triedb_ro_async_traverse(
        TriedbRoInner &inner, NibblesView key, uint64_t block_id,
        ffi::CallbackContext *ctx);

    std::unique_ptr<std::vector<monad::staking::Validator>>
    triedb_ro_read_valset(
        TriedbRoInner &inner, size_t block_num, uint64_t requested_epoch);

    bool triedb_rw_load_root(TriedbRwInner &inner, uint64_t version);

    void triedb_rw_clear_root(TriedbRwInner &inner);

    void triedb_rw_upsert(
        TriedbRwInner &inner, ::rust::Slice<UpsertEntry const> updates,
        uint64_t block_id);

    void triedb_rw_update_proposed_metadata(
        TriedbRwInner &inner, uint64_t version,
        monad::bytes32_t const &block_id);

    void triedb_rw_update_voted_metadata(
        TriedbRwInner &inner, uint64_t version,
        monad::bytes32_t const &block_id);

    void
    triedb_rw_update_finalized_version(TriedbRwInner &inner, uint64_t version);
} // namespace monad::rust
