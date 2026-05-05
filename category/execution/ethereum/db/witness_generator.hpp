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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/node_cursor.hpp>

#include <cstdint>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN
class Db;
MONAD_MPT_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

struct WitnessData
{
    std::vector<byte_string> nodes;
    std::vector<byte_string> codes;
};

/// Build a witness for the just-executed block by walking the live state
/// trie. The verifier replays the block against a `PartialTrieDb`
/// reconstructed from the witness
WitnessData generate_witness(
    mpt::Db &db, mpt::NodeCursor const &accounts_trie_root,
    uint64_t block_number, StateDeltas const &deltas,
    ankerl::unordered_dense::segmented_map<bytes32_t, vm::SharedIntercode> const
        &read_codes,
    SelfDestructStorageReads const &self_destruct_storage_reads);

MONAD_NAMESPACE_END
