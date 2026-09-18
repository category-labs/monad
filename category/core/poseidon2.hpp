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

// Poseidon2 over Goldilocks, width 16, matching ZisK's syscall_poseidon2.
// Round constants come from proofman-fields' poseidon2_constants.rs. Three
// vectors (zero, ramp, near-modulus) check host/precompile agreement.
//
// The byte sponge has rate 88 / capacity 40: lanes 0-10 hold eight bytes
// each; lane 11 records which lanes were reduced. These flags make reduction
// injective while satisfying the AIR's canonical-field-element requirement.

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

    /// Goldilocks: p = 2**64 - 2**32 + 1. Since p + (2**32 - 1) = 2**64,
    /// modular corrections can use addition, which is cheaper than
    /// subtraction on ZisK. Branches skip unnecessary work without a
    /// misprediction cost. These operations are shared by the permutation, L2
    /// sponge and cipher.
    inline constexpr uint64_t GOLDILOCKS_P = 0xFFFFFFFF00000001ULL;

    /// Field addition on canonical operands (both < p). Overflow and sums >=
    /// p both need +2**32-1. The cases are exclusive: correcting an overflow
    /// produces at most p-2, so only one correction is needed.
    constexpr uint64_t
    goldilocks_add(uint64_t const a, uint64_t const b) noexcept
    {
        uint64_t s = a + b;
        if (s < a || s >= GOLDILOCKS_P) {
            s += 0xFFFFFFFFULL;
        }
        return s;
    }

    /// Field subtraction on canonical operands (both < p). On borrow, add p
    /// to the wrapped difference; this addition intentionally wraps to a-b+p.
    constexpr uint64_t
    goldilocks_sub(uint64_t const a, uint64_t const b) noexcept
    {
        uint64_t d = a - b;
        if (a < b) {
            d += GOLDILOCKS_P;
        }
        return d;
    }

    /// Checks the three reference vectors for host/precompile agreement.
    bool poseidon2_test_vectors();

} // namespace monad
