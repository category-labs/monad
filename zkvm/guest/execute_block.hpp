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

/// Execution result; domain_anchor is zero in non-L2 builds. Keep the return
/// type unconditional so callers need no macro-dependent signature.
struct ZkvmBlockOutput
{
    bytes32_t state_root;
    bytes32_t domain_anchor;
};

// Sequential guest execution without the fiber pool or dispatch indirection.
// root_transactions holds original Ethereum transaction bytes or all domain
// ciphertexts (including drops). Only Ethereum checks a transactions root.
// transaction_encodings holds signing bytes for accepted transactions: the
// original slices on Ethereum, decrypted plaintexts on L2.
///
/// Both trait families reach here, so the last two parameters are the Monad
/// arm's alone: ChainContext is empty for EvmTraits and carries five members
/// for MonadTraits, two of which are the sender and authority sets of the
/// PARENT and GRANDPARENT blocks. can_sender_dip_into_reserve reads them to
/// refuse a dip, and a proof of one block cannot derive them, so they arrive
/// in the witness.
template <Traits traits>
    requires(is_monad_trait_v<traits>)
Result<ZkvmBlockOutput> execute_block_zkvm(
    Chain const &chain, Block const &block,
    std::span<byte_string_view const> root_transactions,
    std::span<byte_string_view const> transaction_encodings, Db &pdb,
    vm::VM &vm, BlockHashBuffer const &block_hash_buffer,
    /// Recovered senders, one per transaction, or empty to recover here.
    /// Domain decoding supplies them after applying its recovery-failure drop
    /// rule.
    std::span<Address const> recovered_senders = {},
    ankerl::unordered_dense::segmented_set<Address> const
        *parent_senders_and_authorities = nullptr,
    ankerl::unordered_dense::segmented_set<Address> const
        *grandparent_senders_and_authorities = nullptr);

MONAD_NAMESPACE_END
