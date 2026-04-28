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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

/// A shallowly-parsed Reth witness bundle.
///
/// Only the two fixed-size root hashes (fields [1] and [2]) are eagerly
/// decoded. All other fields are represented as byte_string_view spans
/// pointing into the original witness bytes; the caller must keep that
/// buffer alive for as long as this struct is used.
///
/// Wire format (7-field RLP list):
///   [0] block_rlp        RLP-encoded block
///   [1] pre_state_root   bytes32
///   [2] post_state_root  bytes32
///   [3] [node...]        RLP list of MPT node preimages
///   [4] [code...]        RLP list of contract bytecodes
///   [5] [key...]         RLP list of address/slot preimages (not stored)
///   [6] [header...]      RLP list of ancestor block headers
struct ExecutionWitness
{
    byte_string_view block_rlp;
    bytes32_t pre_state_root;
    bytes32_t post_state_root;
    byte_string_view encoded_nodes;
    byte_string_view encoded_codes;
    byte_string_view encoded_headers;
};

Result<ExecutionWitness>
parse_execution_witness(byte_string_view witness_bytes);

MONAD_NAMESPACE_END
