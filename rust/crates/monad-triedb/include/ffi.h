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
} // namespace monad::rust

#include "monad-triedb/src/ffi.rs.h"

namespace monad::rust
{
    std::unique_ptr<TriedbRoInner> triedb_open(
        ::rust::Str dbdirpath, uint64_t node_lru_max_mem,
        bool disable_mismatching_storage_pool_check);

    inline size_t
    triedb_poll(TriedbRoInner &inner, bool const blocking, size_t const count)
    {
        return inner.db.poll(blocking, count);
    }

    inline uint64_t triedb_latest_proposed_version(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_proposed_version();
    }

    inline uint64_t triedb_latest_voted_version(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_voted_version();
    }

    inline uint64_t triedb_latest_finalized_version(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_finalized_version();
    }

    inline uint64_t triedb_latest_verified_version(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_verified_version();
    }

    inline uint64_t triedb_earliest_version(TriedbRoInner const &inner)
    {
        return inner.db.get_earliest_version();
    }

    inline uint64_t triedb_latest_version(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_version();
    }

    inline monad::bytes32_t
    triedb_latest_proposed_block_id(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_proposed_block_id();
    }

    inline monad::bytes32_t
    triedb_latest_voted_block_id(TriedbRoInner const &inner)
    {
        return inner.db.get_latest_voted_block_id();
    }

    std::unique_ptr<monad::mpt::NodeCursor>
    triedb_read(TriedbRoInner const &inner, NibblesView key, uint64_t block_id);

    void triedb_async_read(
        TriedbRoInner &inner, NibblesView key, uint64_t block_id,
        ffi::CallbackContext *ctx);

    void triedb_traverse(
        TriedbRoInner &inner, NibblesView key, uint64_t block_id,
        ffi::CallbackContext *ctx);

    void triedb_async_ranged_get(
        TriedbRoInner &inner, NibblesView prefix, NibblesView min,
        NibblesView max, uint64_t block_id, ffi::CallbackContext *ctx);

    void triedb_async_traverse(
        TriedbRoInner &inner, NibblesView key, uint64_t block_id,
        ffi::CallbackContext *ctx);

    std::unique_ptr<std::vector<monad::staking::Validator>> triedb_read_valset(
        TriedbRoInner &inner, size_t block_num, uint64_t requested_epoch);
} // namespace monad::rust
