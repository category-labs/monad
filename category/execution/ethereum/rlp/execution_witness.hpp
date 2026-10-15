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

/// Shallow views into the witness buffer, which must outlive this struct.
///
/// Six-field RLP layout:
/// [0] block_rlp: RLP block
/// [1] nodes: offset-format node blob in a list envelope (offset_trie.hpp)
/// [2] [code...]: contract bytecodes
/// [3] [header...]: ancestor headers
/// [4] [address...]: parent sender/authority set
/// [5] [address...]: grandparent sender/authority set
///
/// Fields 4-5 may be empty when reserve-balance rules are inactive.
struct ExecutionWitness
{
    byte_string_view block_rlp;
    byte_string_view encoded_nodes;
    byte_string_view encoded_codes;
    byte_string_view encoded_headers;
    byte_string_view encoded_parent_senders_and_authorities;
    byte_string_view encoded_grandparent_senders_and_authorities;
};

/// Six-field domain witness. Views borrow the input buffer, which must outlive
/// this struct.
///
/// [0] domain_body: RLP-encoded [L1 header, [ciphertexts...],
///     [outer gas limits...], previous domain block number]
/// [1] nodes: offset-format trie node blob in a list envelope
/// [2] [code...]: contract bytecodes
/// [3] [hash...]: 32-byte L1 block hashes used by BLOCKHASH
/// [4] sk: 32-byte big-endian secp256k1 decryption scalar
/// [5] salt_secret: 32-byte seed for per-block state blinders
///
/// MONAD_ZKVM_L2 selects this parser. Field [4] distinguishes the formats:
/// an RLP string here, an address list in the mainnet witness.
/// The domain uses empty parent/grandparent sender and authority sets,
/// matching the client; these sets are not supplied in the witness.
///
/// The guest binds sk to the configured operator key and salt_secret to its
/// configured commitment. Seed generation must still provide secret entropy;
/// the commitment check does not establish it.
struct ExecutionWitnessL2
{
    byte_string_view domain_body;
    byte_string_view encoded_nodes;
    byte_string_view encoded_codes;
    byte_string_view encoded_ancestor_hashes;
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

/// Encode the six fields of ExecutionWitnessL2. Each ancestor hash, sk and
/// salt_secret must be exactly 32 bytes.
byte_string encode_execution_witness_l2(
    byte_string_view domain_body, byte_string_view nodes,
    std::span<byte_string const> codes,
    std::span<byte_string const> ancestor_hashes, byte_string_view sk,
    byte_string_view salt_secret);

MONAD_NAMESPACE_END
