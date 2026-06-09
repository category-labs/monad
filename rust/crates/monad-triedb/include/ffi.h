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
    inline ::rust::Slice<uint8_t const>
    node_cursor_as_bytes(monad::mpt::NodeCursor const &cursor)
    {
        auto const &val = cursor.node->value();
        return {val.data(), val.size()};
    }

    struct TriedbRoInner
    {
        monad::mpt::AsyncIOContext io_ctx;
        monad::mpt::Db db;
        monad::mpt::AsyncContext async_ctx;

        explicit TriedbRoInner(
            std::vector<std::filesystem::path> dbname_paths,
            uint64_t node_lru_max_mem);
    };

    std::unique_ptr<TriedbRoInner>
    triedb_open(::rust::Str dbdirpath, uint64_t node_lru_max_mem);

    // pumps async reads, processing no more than count maximum, returning how
    // many were processed.
    inline size_t
    triedb_poll(TriedbRoInner &db, bool const blocking, size_t const count)
    {
        return db.db.poll(blocking, count);
    }

    // returns MAX if doesn't exist
    inline uint64_t triedb_latest_proposed_version(TriedbRoInner const &db)
    {
        return db.db.get_latest_proposed_version();
    }

    // returns MAX if doesn't exist
    inline uint64_t triedb_latest_voted_version(TriedbRoInner const &db)
    {
        return db.db.get_latest_voted_version();
    }

    // returns MAX if doesn't exist
    inline uint64_t triedb_latest_finalized_version(TriedbRoInner const &db)
    {
        return db.db.get_latest_finalized_version();
    }

    // returns MAX if doesn't exist
    inline uint64_t triedb_latest_verified_version(TriedbRoInner const &db)
    {
        return db.db.get_latest_verified_version();
    }

    // returns MAX if doesn't exist
    inline uint64_t triedb_earliest_version(TriedbRoInner const &db)
    {
        return db.db.get_earliest_version();
    }

    // returns MAX if doesn't exist
    inline uint64_t triedb_latest_version(TriedbRoInner const &db)
    {
        return db.db.get_latest_version();
    }

    // returns all-zeros if doesn't exist
    inline monad::bytes32_t
    triedb_latest_proposed_block_id(TriedbRoInner const &db)
    {
        return db.db.get_latest_proposed_block_id();
    }

    // returns all-zeros if doesn't exist
    inline monad::bytes32_t
    triedb_latest_voted_block_id(TriedbRoInner const &db)
    {
        return db.db.get_latest_voted_block_id();
    }

    std::unique_ptr<std::vector<uint8_t>> triedb_read(
        TriedbRoInner const &db, ::rust::Slice<uint8_t const> const key,
        uint8_t const key_len_nibbles, uint64_t const block_id);

    void triedb_async_read(
        TriedbRoInner &db, ::rust::Slice<uint8_t const> key,
        uint8_t key_len_nibbles, uint64_t block_id, ffi::CallbackContext *ctx);

    void triedb_traverse(
        TriedbRoInner &db, ::rust::Slice<uint8_t const> key,
        uint8_t key_len_nibbles, uint64_t block_id, ffi::CallbackContext *ctx);

    void triedb_async_traverse(
        TriedbRoInner &db, ::rust::Slice<uint8_t const> key,
        uint8_t key_len_nibbles, uint64_t block_id, ffi::CallbackContext *ctx);

    void triedb_async_traverse_range(
        TriedbRoInner &db, ::rust::Slice<uint8_t const> prefix_key,
        uint8_t prefix_key_len_nibbles, ::rust::Slice<uint8_t const> min_key,
        uint8_t min_key_len_nibbles, ::rust::Slice<uint8_t const> max_key,
        uint8_t max_key_len_nibbles, uint64_t block_id,
        ffi::CallbackContext *ctx);

    std::unique_ptr<std::vector<monad::staking::Validator>> triedb_read_valset(
        TriedbRoInner &db, size_t block_num, uint64_t requested_epoch);
} // namespace monad::rust
