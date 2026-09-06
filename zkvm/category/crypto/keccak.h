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

// Shared zkVM shadow of category/crypto/keccak.h. The host declares
// monad_keccak256() and defines it out of line over OpenSSL's SHA3 core; the
// guest binds it always_inline here, so the two cannot share a declaration.
// Everything else callers use from the host header is reproduced below.
//
// The shadow is on the include path of the guest targets only -- the x86 test
// runner is built without it -- so a backend is always defined and there is no
// host arm.

#pragma once

#include <stddef.h>
#include <stdint.h>

constexpr size_t KECCAK256_SIZE = 32;

// Both backends: enter the permutation precompile through a word-wise absorb
// (zkvm/guest/keccak_accel.cpp). The stock wrappers marshal the sponge byte by
// byte -- zisklib's at ~400-530 steps per permutation, SP1's via tiny_keccak's
// software sponge at 19.5 % of the guest's attributed work.
extern "C" void monad_zkvm_keccak256_fast(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

// The same digest with the Keccak-f memo compiled out, for an input whose
// permutations cannot repeat -- see the entry point's own comment for why
// contract bytecode is the one such caller and why not filing is sound. It has
// no host counterpart, so callers name it directly rather than through a
// shadowed name.
extern "C" void monad_zkvm_keccak256_fast_nomemo(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

[[gnu::always_inline]] static inline void monad_keccak256(
    void const *const in, size_t const len, uint8_t out[KECCAK256_SIZE])
{
    monad_zkvm_keccak256_fast(in, len, out);
}
