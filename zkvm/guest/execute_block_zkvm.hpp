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
struct Db;
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
// `raw_transactions` is the byte slice each transaction was decoded from, in
// order, as decode_block hands them out. The transactions-root check uses
// those bytes directly rather than re-encoding what was decoded from them --
// see the note at the body binding.
template <Traits traits>
Result<bytes32_t> execute_block_zkvm(
    Chain const &chain, Block const &block,
    std::span<byte_string_view const> raw_transactions, Db &pdb, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    ChainContext<traits> const &chain_ctx);

MONAD_NAMESPACE_END
