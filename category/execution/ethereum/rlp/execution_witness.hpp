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
/// ExecutionWitnessL2 adds two fields. Strict length checks distinguish the
/// six- and eight-field shapes; MONAD_ZKVM_L2 selects the parser at build
/// time.
struct ExecutionWitness
{
    byte_string_view block_rlp;
    byte_string_view encoded_nodes;
    byte_string_view encoded_codes;
    byte_string_view encoded_headers;
    byte_string_view encoded_parent_senders_and_authorities;
    byte_string_view encoded_grandparent_senders_and_authorities;
};

/// L2 adds two private fields:
/// [6] sk: 32-byte big-endian secp256k1 decryption scalar
/// [7] salt_secret: 32 bytes used to derive per-block state blinders
///
/// The guest binds sk to the operator key to prevent arbitrary decryption. It
/// binds salt_secret to a compiled commitment to prevent arbitrary,
/// predictable blinders. This second check protects confidentiality, not
/// state-transition soundness; the seed must still be generated securely.
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
