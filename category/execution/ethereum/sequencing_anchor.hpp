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

// Sequencing anchor over every ciphertext handed to the guest, including
// rejected entries, in L1 order:
//
// anchor = keccak256(LABEL || chainId_be64 || number_be64
// || keccak256(ct_1) || ... || keccak256(ct_n))
//
// The verifier must compare this with the L1-sequenced inputs to detect
// omissions or reordering. Hashing plaintext or only accepted entries would
// let the prover choose the input set.
//
// Leaf hashes remove variable-length concatenation ambiguity. Keccak keeps L1
// verification native. One outer sponge reduces guest permutations but
// requires L1 to hold all leaf hashes; it is not an incremental accumulator.
// See zkvm/DECISIONS.md for the tradeoff.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

/// Absorbed first so this digest cannot be mistaken for, or replayed as, any
/// other keccak256 this protocol computes. Bumped if the construction changes
/// at all.
inline constexpr char SEQUENCING_ANCHOR_LABEL[] =
    "monad-domain/sequencing-anchor/v1";

/// Anchor all sequenced leaves, including rejected ones, in L1 order. Domain
/// and height prevent cross-domain/block replay. An empty block hashes the
/// preamble, rather than using zero as both an anchor and an unset value.
bytes32_t sequencing_anchor(
    uint64_t domain_chain_id, uint64_t block_number,
    std::span<byte_string_view const> ciphertexts);

MONAD_NAMESPACE_END
