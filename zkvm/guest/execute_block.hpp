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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/vm/evm/traits.hpp>

#include <span>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct Block;
class State;

// The guest's block loop: the sequential mirror of execute_block<traits>,
// driving the one guest State the witness built. The block prologue, every
// transaction and the post-block steps run against `state` in order, then
// commit writes the result to the trie and the post-state root comes back.
// Drops the fiber pool, the per-transaction State and merge, the tracers
// and the metrics of the native path.
template <Traits traits>
    requires(is_evm_trait_v<traits>)
Result<bytes32_t> execute_block_zkvm(
    Chain const &chain, Block const &block,
    std::span<byte_string_view const> raw_transactions, State &state,
    BlockHashBuffer const &block_hash_buffer);

MONAD_NAMESPACE_END
