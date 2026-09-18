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

// Poseidon2 over Goldilocks, width 16, and a 32-byte sponge over it.
//
// The permutation is the one ZisK's `syscall_poseidon2` implements. Its round
// constants are extracted from proofman-fields' poseidon2_constants.rs rather
// than transcribed, and poseidon2_test_vectors() checks three of them -- one
// all-zero, one ramp, one with lanes just under the modulus -- against outputs
// taken from both that crate's native path and the ZisK precompile, which
// agree. A guest build routes the permutation to the precompile; this file is
// what the host computes, so a witness generator and the guest produce the same
// digest.
//
// The sponge is rate 88 / capacity 40: lanes 0-10 carry eight bytes each and
// lane 11 carries one "was reduced" bit per data lane. Eight arbitrary bytes
// are not always canonical and the Poseidon AIR enforces canonicity on the
// memory rows (precompiles/poseidon/pil, an is-zero gadget on MASK_32 - hi), so
// a lane at or above the modulus is unprovable; the flags lane keeps the
// reduction injective, where a bare conditional subtract would let two inputs
// differing by p in one lane collide.

#pragma once

#include <cstddef>
#include <cstdint>

extern "C"
{
/// The permutation, in place. 16 Goldilocks lanes, each < 2**64 - 2**32 + 1.
void monad_poseidon2_16(uint64_t state[16]);

/// Sponge: absorb `len` bytes, squeeze a 32-byte digest.
void monad_poseidon2_256(void const *in, size_t len, unsigned char out[32]);
}

namespace monad
{

    /// Goldilocks: p = 2**64 - 2**32 + 1.
    ///
    /// The one identity both operations below turn on: p + (2**32 - 1) is
    /// exactly 2**64. Read one way, -p is +2**32-1 modulo 2**64; read the
    /// other, -(2**32 - 1) is +p. So every correction either of them needs is
    /// an ADDITION, and the subtract that would read more naturally in each
    /// case is never necessary.
    ///
    /// Which matters because of what ZisK charges: 68 a step, plus 25 for an
    /// add against 60 for a sub or a compare (MAIN_COST, BINARY_ADD_COST and
    /// BINARY_COST at zisk v1.1.0-alpha, the revision the Cargo.lock pins). A
    /// subtract is 35 dearer than an add, and an avoided instruction is worth
    /// 68 on its own.
    ///
    /// Both are written BRANCHED rather than with a mask, which inverts the
    /// usual advice deliberately: a zkVM has no speculation and no
    /// misprediction, so cost is the instructions retired and a branch that
    /// skips work is a pure win, where on a real core one would reach for a
    /// mask to avoid the stall. The branchless forms execute strictly more
    /// instructions here.
    ///
    /// Both are also exported rather than kept file-local to poseidon2.cpp,
    /// because the permutation is not the only thing that needs the field: the
    /// L2 sponge absorbs with it and the cipher's masks are applied with it,
    /// and a second copy of this arithmetic would be a second thing to keep in
    /// step with the AIR.
    inline constexpr uint64_t GOLDILOCKS_P = 0xFFFFFFFF00000001ULL;

    /// Field addition, on CANONICAL operands only (both < p).
    ///
    /// The two corrections are the same addition of the same constant. A
    /// wrapped sum owes back the 2**64 it dropped, which is 2**32-1 modulo p;
    /// an unwrapped sum at or above p owes -p, which is the same thing by the
    /// identity above.
    ///
    /// They are also mutually exclusive, so the correction applies at most
    /// once: a wrapped sum is at most 2**64 - 2**33, and +2**32-1 leaves it at
    /// most 2**64 - 2**32 - 1, two below p. The short-circuit therefore skips
    /// the second compare exactly when the first fires.
    constexpr uint64_t
    goldilocks_add(uint64_t const a, uint64_t const b) noexcept
    {
        uint64_t s = a + b;
        if (s < a || s >= GOLDILOCKS_P) {
            s += 0xFFFFFFFFULL;
        }
        return s;
    }

    /// Field subtraction, on CANONICAL operands only (both < p).
    ///
    /// On a borrow the wrapped difference is a - b + 2**64 and the answer is
    /// a - b + p, so the correction is -(2**32 - 1) -- which is +p by the
    /// identity above. That addition is meant to wrap: it lands on the answer
    /// modulo 2**64, which is the representative wanted.
    ///
    /// The a - b itself stays a subtract, b being a variable rather than a
    /// constant the modulus can be folded into.
    constexpr uint64_t
    goldilocks_sub(uint64_t const a, uint64_t const b) noexcept
    {
        uint64_t d = a - b;
        if (a < b) {
            d += GOLDILOCKS_P;
        }
        return d;
    }

    /// True when the permutation reproduces the three reference vectors. A port
    /// that drifts from the precompile is otherwise silent: the generator would
    /// emit a witness whose digests the guest recomputes differently, and the
    /// only symptom would be a root mismatch with no indication of which side
    /// is wrong.
    bool poseidon2_test_vectors();

} // namespace monad
