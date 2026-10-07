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

// Domain input uses the sequencing L1 header, not a separate domain header:
//
// [ L1 header, [ciphertext...], [outer gas limit...], parent number ]
//
// Execution reads number, timestamp, beneficiary, prev_randao, gas_limit and
// base_fee_per_gas from the L1 header. Its body roots, bloom and gas_used
// describe L1 and are not checked against domain execution.
//
// Ciphertexts contain all sequenced payloads in L1 order, before filtering.
// Each outer gas limit bounds its inner transaction's requested gas. Parent
// number identifies the previous domain transition, which can be earlier than
// number-1; it is used to reopen its blinded state commitment.
//
// Match the client's five drop rules: decryption failure, invalid/trailing
// transaction RLP, insufficient outer gas, missing/wrong chain id, or failed
// sender recovery. Dropped entries are consumed without halting the block.
// Return recovered senders so execution need not recover them again.

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <zkvm/guest/l2_cipher_suite.hpp>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct DomainBody
{
    /// `header` is the L1 header; `transactions` are the ACCEPTED payloads,
    /// decrypted, in order. `ommers` and `withdrawals` stay empty: there is no
    /// body for them to come from.
    Block block;
    /// One per accepted transaction, in order. Recovered while dropping, so
    /// execution takes them rather than recovering again.
    std::vector<Address> senders;
    /// The previous domain block's number, for the pre-state blinder.
    uint64_t parent_number{};
};

/// Decode and decrypt the domain body. ciphertexts retains all payloads in
/// order, including drops, for the sequencing anchor. encodings holds
/// accepted plaintext views into plaintexts. Create these views only after
/// appending finishes; plaintexts must outlive them. The caller obtains a
/// context-bound secret through L2Cipher::bind_secret.
Result<DomainBody> decode_domain_body(
    byte_string_view &enc, L2Cipher::Context const &ctx,
    L2Cipher::Secret const &secret, uint64_t domain_chain_id,
    std::vector<byte_string_view> &ciphertexts, byte_string &plaintexts,
    std::vector<byte_string_view> &encodings);

MONAD_NAMESPACE_END
