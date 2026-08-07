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

// Guest-only header: inline monad_keccak256 and select the backend.
// The host and x86 runner keep category/crypto/keccak.h.

#pragma once

#include <stddef.h>
#include <stdint.h>

constexpr size_t KECCAK256_SIZE = 32;

#ifdef MONAD_ZKVM_ZISK

// Dedicated ZisK sponge, implemented in zkvm/guest/keccak_accel.cpp.
extern "C" void monad_zkvm_keccak256_fast(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

[[gnu::always_inline]] static inline void monad_keccak256(
    void const *const in, size_t const len, uint8_t out[KECCAK256_SIZE])
{
    monad_zkvm_keccak256_fast(in, len, out);
}

#else

// SP1 keeps ethash's sponge; define monad_keccakf1600 before including it.
    #include <category/crypto/keccakf1600.h>

    #include <category/crypto/ethash_vendor/keccak.h>

#endif
