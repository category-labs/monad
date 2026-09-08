// Copyright (C) 2026 Category Labs, Inc.
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

// Per-block persistence of the multi-block cache stamp records: one
// sequential blob per block, keccak-hashed (the hash is the consensus
// commitment; its placement is a consensus-team decision). Restart and
// bootstrap rebuild the stamp table and windows by replaying the blobs of
// the live window; files older than the window can be dropped.

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>

#include <cstdint>
#include <filesystem>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct StampBlob
{
    uint64_t block;
    std::vector<AccountStampRecord> account_stamps;
    std::vector<StorageStampRecord> storage_stamps;
};

// Serialize one block's stamp records to <dir>/<block>.blob with a trailing
// keccak256 of the payload.
void write_stamp_blob(
    std::filesystem::path const &dir, uint64_t block,
    std::vector<AccountStampRecord> const &accounts,
    std::vector<StorageStampRecord> const &storage);

// Read and hash-verify one blob; nullopt on malformed content.
std::optional<StampBlob> read_stamp_blob(std::filesystem::path const &file);

// Blob block numbers present in dir, ascending.
std::vector<uint64_t> list_stamp_blobs(std::filesystem::path const &dir);

MONAD_NAMESPACE_END
