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

/// What the proof publishes about a block.
///
/// `namespace_anchor` is bytes32_t{} on a build without MONAD_ZKVM_L2, where
/// there is no spoke to harvest. The struct is unconditional, and the 32 zero
/// bytes are the price: making it conditional would leak the macro into this
/// header, into ffi.cpp's dispatch wrapper, and into the return type of the
/// SWITCH_EVM_TRAITS lambda.
struct ZkvmBlockOutput
{
    bytes32_t state_root;
    bytes32_t namespace_anchor;
};

// Sequential mirror of execute_block<traits> for the zkVM guest. Drops the
// fiber pool, dispatch_transaction indirection, tracers, and block-metrics
// timing; reuses ExecuteTransaction, execute_block_header, process_requests,
// apply_block_reward, and BlockState::merge unchanged.
//
// Receipts are computed and checked against the header, then discarded: what
// leaves here is the post-state root, and under MONAD_ZKVM_L2 the message
// anchor with it.
//
// `root_transactions` is what the transactions-root check is taken over, in
// order. On a plaintext block that is the byte slice each transaction was
// decoded from, one per transaction. On an L2 block it is every ciphertext
// LEAF -- including the ones that were rejected, because the header commits to
// the whole list -- so it may be LONGER than block.transactions. See the note
// at the body binding for why the root is taken over those bytes.
template <Traits traits>
Result<ZkvmBlockOutput> execute_block_zkvm(
    Chain const &chain, Block const &block,
    std::span<byte_string_view const> root_transactions, Db &pdb, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    ChainContext<traits> const &chain_ctx);

MONAD_NAMESPACE_END
