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

// The domain's input for one block, which is NOT a block.
//
// A domain has no blocks of its own. Its transactions are sequenced on the L1,
// one `sequenceToDomain(uint64,bytes)` call each, and the execution client runs
// them against the **L1 header** of the block that sequenced them -- the only
// domain "header" it ever writes is a two-field record, {state_root, number},
// for finalized-root validation. So there is no domain block to decode: no
// transactions root over the ciphertexts, no ommers, no withdrawals, and
// nothing a header of the domain's own could commit to.
//
// What the guest is handed instead is this body:
//
//   [ L1 header, [ciphertext...], [outer gas limit...], parent number ]
//
//   L1 header         the header execution reads -- number, timestamp,
//                     beneficiary, prev_randao, gas_limit, base_fee_per_gas.
//                     Its other fields describe the L1 block and mean nothing
//                     here, which is why the epilogue's block-shaped checks are
//                     gated out on this path: a transactions root or a gas_used
//                     taken from it would be the L1's, not the domain's.
//   ciphertexts       every payload the L1 sequenced for this domain at this
//                     height, in L1 order, before any drop rule.
//   outer gas limits  one per ciphertext, the gas limit of the L1 envelope
//                     that carried it. Needed because an inner transaction
//                     asking for more than its envelope sponsored is dropped,
//                     and that is a fact about the L1 transaction which nothing
//                     downstream of here can see.
//   parent number     the previous domain block's number. Not `number - 1`:
//                     the sequence is sparse, since an L1 block that sequences
//                     nothing for this domain produces no domain block at all.
//                     It is what the pre-state commitment is blinded with, so
//                     that commitment is byte for byte what the previous run
//                     published as its final state.
//
// The decision rule is the protocol's and not the cipher's: a payload the suite
// refuses is CONSUMED and skipped, never a halt. All five of the client's drop
// rules live here -- decryption, a plaintext that is not exactly one
// transaction, the envelope's gas limit, a chain id that is not this domain's,
// and a sender that does not recover. Each is a log line and nothing more over
// there, so each is a skip here; the alternative, failing the block, would
// reject one every replica executes happily.
//
// The sender is recovered here rather than in execution because dropping on it
// means having it before the block is formed. It is handed back so execution
// does not repeat an ECDSA recovery per transaction.

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

/// Decodes the body above, decrypting each payload.
///
/// `ciphertexts` receives EVERY payload, in order, as a view into `enc` --
/// including the dropped ones, because what the sequencing anchor commits to is
/// what the L1 sequenced and not what survived. `ciphertexts.size() -
/// block.transactions.size()` is how many were dropped.
///
/// `encodings` receives, for each accepted transaction in order, the plaintext
/// it was decoded from -- canonical RLP, so a signing payload can be built from
/// those bytes rather than re-encoded field by field. The views point into
/// `plaintexts`, which is appended to as the list is walked; they are only made
/// once the walk is done, so the buffer's growth cannot leave one dangling, and
/// it has to outlive them.
///
/// `secret` arrives already bound to `ctx` -- L2Cipher::bind_secret is the only
/// way to obtain one -- so the check the whole design rests on is carried by
/// the type rather than by a line in this function.
Result<DomainBody> decode_domain_body(
    byte_string_view &enc, L2Cipher::Context const &ctx,
    L2Cipher::Secret const &secret, uint64_t domain_chain_id,
    std::vector<byte_string_view> &ciphertexts, byte_string &plaintexts,
    std::vector<byte_string_view> &encodings);

MONAD_NAMESPACE_END
