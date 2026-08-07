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

#ifdef MONAD_ZKVM_ZISK

// ZisK: enter the precompile through a word-wise absorb
// (zkvm/guest/keccak_accel.cpp). zisklib's zkvm_keccak256 assembles the sponge
// state byte by byte -- ~400-530 steps of marshalling per permutation.
extern "C" void monad_zkvm_keccak256_fast(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

[[gnu::always_inline]] static inline void monad_keccak256(
    void const *const in, size_t const len, uint8_t out[KECCAK256_SIZE])
{
    monad_zkvm_keccak256_fast(in, len, out);
}

#else

// SP1 keeps the vendored ethash sponge over the backend's permutation. Include
// order matters: the sponge calls monad_keccakf1600() without declaring it, so
// the backend's definition has to be in scope first.
    #include <category/crypto/keccakf1600.h>

    #include <category/crypto/ethash_vendor/keccak.h>

#endif
