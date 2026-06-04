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

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class PartialTrieDb;
struct Block;

namespace vm
{
    class VM;
}

// Sequential mirror of execute_block<traits> for the zkVM guest. Drops the
// fiber pool, dispatch_transaction indirection, tracers, and block-metrics
// timing; reuses ExecuteTransaction, execute_block_header, process_requests,
// apply_block_reward, and BlockState::merge unchanged.
//
// MVP: emits the post-state root only. Receipts are computed (and the YP eq.22
// cumulative-gas fixup is applied) but discarded; Phase 7 wires them into a
// full block-output hash.
template <Traits traits>
Result<bytes32_t> execute_block_zkvm(
    Chain const &chain, Block const &block, PartialTrieDb &pdb, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    ChainContext<traits> const &chain_ctx);

MONAD_NAMESPACE_END
