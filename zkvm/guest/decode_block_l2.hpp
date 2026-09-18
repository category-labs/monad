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

// Block decoding for the L2, where the transactions list holds ciphertexts.
//
// It mirrors rlp::decode_block and DELEGATES to the same decoders for the
// header, the ommers and the withdrawals -- only the transactions walk is new
// code. That keeps the duplication to the one list that actually differs, and
// decode_block_l2_test asserts the two agree on everything else, so a field
// added to one and not the other is a failing test rather than a wrong root.
//
// Every item of the list is an RLP STRING whose content is the leaf, for every
// transaction type. There is deliberately no dispatch on `items[0] >= 0xc0` the
// way the plaintext walk does: a ciphertext byte is uniform, so that test would
// be a coin flip. Uniform string framing is what removes the ambiguity, and it
// is also why a ciphertext leaf can never be mistaken for a legacy list.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <zkvm/guest/l2_cipher_suite.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;

/// Decodes an L2 block, decrypting each leaf.
///
/// `ciphertexts` receives EVERY leaf, in order, as a view into `enc` -- that is
/// what the transactions root is taken over, and it includes the rejected ones
/// because the header commits to the whole list.
///
/// `block.transactions` receives only the ACCEPTED ones. A leaf whose envelope
/// is malformed, whose R is not a curve point, whose tag does not verify, or
/// whose plaintext is not exactly one RLP transaction is REJECTED: the entry is
/// consumed, nothing is executed for it, no receipt is produced, and the block
/// stays valid. That is the protocol's rule, and it is why the two vectors can
/// differ in length -- `ciphertexts.size() - block.transactions.size()` is the
/// number rejected.
///
/// The per-leaf "nothing left over" check is stricter than the plaintext list
/// walk can be: there, one item's trailing bytes are the next item's leading
/// bytes, so a short declared length desynchronises the walk instead of
/// failing.
///
/// The cipher is reached only through the selected suite (l2_cipher_suite.hpp),
/// so nothing here names a curve, a field or a leaf format -- swapping the
/// encryption does not touch this file. What this file does own is the
/// DECISION RULE, which is not the suite's to change: a leaf the suite refuses
/// is consumed and skipped, never a halt.
///
/// `secret` arrives already bound to `ctx` -- L2Cipher::bind_secret is the only
/// way to obtain one, and it fails unless the witness's bytes are the secret
/// the context names. So the check every other part of this design rests on is
/// carried by the type rather than by a line in this function: there is no way
/// to call it with an unbound secret, and a malformed witness halts in ffi.cpp
/// alongside every other witness defect.
Result<Block> decode_block_l2(
    byte_string_view &enc, L2Cipher::Context const &ctx,
    L2Cipher::Secret const &secret, std::vector<byte_string_view> &ciphertexts);

MONAD_NAMESPACE_END
