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

// The sequencing anchor: a digest of the ciphertexts the L1 sequenced for one
// domain at one block, published so a verifier can tell WHICH inputs produced
// the state the proof attests.
//
// Without it the published tuple pins the result of a computation and not its
// inputs. An ordinary chain gets this free -- a block hash covers
// transactions_root -- but a domain has no block header of its own, so nothing
// does it. A validator quorum covers the gap socially, since independent
// replicas read the same L1 calldata and will not sign a root obtained from a
// different set; a single proof replacing that quorum removes the cover, and a
// prover that executes a subset, or a permutation, produces a root that is
// perfectly valid for THAT computation and that the hub cannot distinguish.
//
// It lives beside domain_anchor.hpp and for the same reason: the rule has to
// match what the L1 computes bit for bit, and the guest, the corpus generator
// and eventually the node all need it. A rule duplicated across translation
// units that no build step keeps in step is the likeliest way this breaks.
//
//   anchor = H(LABEL ‖ chainId_be64 ‖ number_be64 ‖ H(ct_1) ‖ … ‖ H(ct_n))
//
// with H the chain's hash, MONAD_ZKVM_L2_HASH: keccak256 in a keccak chain, the
// Poseidon2 sponge (monad_poseidon2_256) in a Poseidon2 one.
//
// Four properties, each of which could have been chosen otherwise -- see
// zkvm/DECISIONS.md, which records why:
//
//   over CIPHERTEXTS, not decrypted transactions. The hub never sees plaintext,
//   so a digest over the decrypted form is checkable only by someone who
//   already holds the viewing key, which is to say it binds nothing from the
//   L1's point of view.
//
//   over the SEQUENCED set, not the executed one. A leaf the cipher refuses is
//   consumed and skipped rather than halting the block, and the drop rules are
//   exactly where a dishonest prover would cheat -- so a digest taken after
//   them lets the prover certify its own choices. Every leaf goes in, in L1
//   order, and the rules are applied deterministically afterwards.
//
//   THE CHAIN'S HASH, like the other hashes this chain defines. In a keccak
//   chain that is the hash the verifier has: the EVM's opcode, 30 gas a word,
//   so a hub recomputes its half at L1 prices. A Poseidon2 chain takes
//   Poseidon2 here too: cheap where the chain is proved, on ZisK's precompile
//   and with no Keccak-f at all, which matters most where the chain's other
//   keccak runs in software (MONAD_ZKVM_KECCAKF_SOFTWARE); and dear where it is
//   checked, since the EVM has no Poseidon2 -- a permutation costs thousands of
//   gas in Solidity, and a hub recomputing this pays that at every transition.
//   zkvm/DECISIONS.md records the trade.
//
//   ONE sponge over the whole preamble and leaf-hash vector, rather than a
//   hash chained one leaf at a time. The chained form is what an L1-side
//   accumulator could maintain incrementally, and this one forecloses that: the
//   EVM's keccak256 is all-or-nothing over a memory range, so a hub computing
//   this must hold every leaf hash at once. In exchange it costs 0.765 fewer
//   keccak permutations per sequenced transaction (136-byte rate), or 0.636
//   fewer Poseidon2 ones (88-byte rate) -- the chained form pays a whole
//   permutation per leaf where this one absorbs 32 bytes into a sponge that is
//   running anyway. Free under the Keccakf precompile, where a block
//   stays well inside one 14,462-permutation instance either way; not free
//   under MONAD_ZKVM_KECCAKF_SOFTWARE, which is what decided it.
//
// Each leaf is hashed before being absorbed, which is orthogonal to the above
// and not negotiable: it keeps every element a fixed 32 bytes and removes the
// splitting ambiguity a raw concatenation of variable-length leaves would
// carry, where `ab`,`c` and `a`,`bc` hash alike.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

/// Absorbed first so this digest cannot be mistaken for, or replayed as, any
/// other digest this protocol computes under the same hash. Bumped if the
/// construction changes at all; the hash is the chain's, a property of the
/// chain rather than of this construction, so the two chains share it.
inline constexpr char SEQUENCING_ANCHOR_LABEL[] =
    "monad-domain/sequencing-anchor/v1";

/// The anchor over a whole block's leaves, in sequencing order.
///
/// `ciphertexts` must be EVERY leaf the L1 sequenced for this domain at this
/// block, rejected ones included -- decode_block_l2's `ciphertexts` output is
/// exactly that set.
///
/// The domain and the height are bound so a digest cannot replay across domains
/// or across blocks of one domain. A block that sequenced nothing anchors to
/// the preamble alone rather than to zero, which keeps "nothing at this height"
/// a statement the proof makes rather than a value indistinguishable from an
/// unset field.
bytes32_t sequencing_anchor(
    uint64_t domain_chain_id, uint64_t block_number,
    std::span<byte_string_view const> ciphertexts);

MONAD_NAMESPACE_END
