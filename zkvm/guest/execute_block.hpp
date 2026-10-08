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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

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
// `parent_senders_and_authorities` and `grandparent_senders_and_authorities`
// are the two ancestor sets can_sender_dip_into_reserve reads. A proof of one
// block cannot derive them -- they belong to blocks it does not carry -- so
// they arrive in the witness and their hash is published, which leaves the
// verifier, who has the chain, to say whether they are the right ones.
template <Traits traits>
    requires(is_monad_trait_v<traits>)
Result<bytes32_t> execute_block_zkvm(
    Chain const &chain, Block const &block,
    std::span<byte_string_view const> raw_transactions, Db &pdb, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    ankerl::unordered_dense::segmented_set<Address> const
        &parent_senders_and_authorities,
    ankerl::unordered_dense::segmented_set<Address> const
        &grandparent_senders_and_authorities);

MONAD_NAMESPACE_END
