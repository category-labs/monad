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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

/// A shallowly-parsed witness bundle. Every field is a byte_string_view
/// pointing into the original witness bytes; the caller must keep that
/// buffer alive for as long as this struct is used.
///
/// Wire format (6-field RLP list):
///   [0] block_rlp                     RLP-encoded block
///   [1] nodes                         offset-format node blob (see
///                                     offset_trie.hpp) in a list envelope
///   [2] [code...]                     RLP list of contract bytecodes
///   [3] [header...]                   RLP list of ancestor block headers
///   [4] [address...]                  Parent sender+authority set
///   [5] [address...]                  Grandparent sender+authority set
///
/// Fields [4] and [5] can be left unpopulated for chains/revisions where
/// can_sender_dip_into_reserve is not active (EVM traits, pre-MONAD_FOUR).
///
/// An L2 witness carries two further fields and is parsed by
/// parse_execution_witness_l2; see ExecutionWitnessL2. There is deliberately no
/// version byte in the envelope: the strict trailing-byte rejection at both
/// levels already makes each shape reject the other loudly, six fields against
/// eight, and a version would buy a runtime dispatch that the compile-time
/// MONAD_ZKVM_L2 switch says we do not want. Were one ever needed it would have
/// to be a new field [0] -- a version cannot sit after what it describes.
struct ExecutionWitness
{
    byte_string_view block_rlp;
    byte_string_view encoded_nodes;
    byte_string_view encoded_codes;
    byte_string_view encoded_headers;
    byte_string_view encoded_parent_senders_and_authorities;
    byte_string_view encoded_grandparent_senders_and_authorities;
};

/// An L2 witness: the six fields above plus
///   [6] sk           the block's transaction-decryption secret: a secp256k1
///                    scalar as 32 BIG-ENDIAN bytes, the same order a
///                    signature's r and s arrive in
///   [7] salt_secret  32 bytes the per-block state blinder is derived from
///
/// Both are private inputs, and both are why the guest has a binding check for
/// them. For sk the argument is direct: without checking sk*G against the
/// operator key the protocol names, a prover supplies any secret, decrypts to
/// a different set of transactions, and proves a perfectly valid post-state
/// for a block nobody wrote.
///
/// For salt_secret the failure is quieter and worth spelling out, because it
/// does not look like a failure. An unbound blinder costs nothing in
/// soundness -- the commitment chain forces a prover to reuse whatever it
/// chose, and keccak256 binds it -- so every proof still verifies and every
/// block still chains. What breaks is the confidentiality the blinder exists
/// for: a producer that supplies zeros publishes an unblinded block hash, and
/// the state becomes testable by anyone who can guess it. Nothing detects
/// that, which is why the secret is checked against a compiled commitment
/// rather than trusted.
struct ExecutionWitnessL2
{
    ExecutionWitness base;
    byte_string_view sk;
    byte_string_view salt_secret;
};

Result<ExecutionWitness>
parse_execution_witness(byte_string_view witness_bytes);

Result<ExecutionWitnessL2>
parse_execution_witness_l2(byte_string_view witness_bytes);

byte_string encode_execution_witness(
    byte_string_view block_rlp, byte_string_view nodes,
    std::span<byte_string const> codes, std::span<byte_string const> headers,
    ankerl::unordered_dense::segmented_set<Address> const
        *const parent_senders_and_authorities = nullptr,
    ankerl::unordered_dense::segmented_set<Address> const
        *const grandparent_senders_and_authorities = nullptr);

/// The same, plus field [6]. `sk` must be exactly 32 bytes.
byte_string encode_execution_witness_l2(
    byte_string_view block_rlp, byte_string_view nodes,
    std::span<byte_string const> codes, std::span<byte_string const> headers,
    byte_string_view sk, byte_string_view salt_secret,
    ankerl::unordered_dense::segmented_set<Address> const
        *const parent_senders_and_authorities = nullptr,
    ankerl::unordered_dense::segmented_set<Address> const
        *const grandparent_senders_and_authorities = nullptr);

MONAD_NAMESPACE_END
