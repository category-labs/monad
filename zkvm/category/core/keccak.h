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

// Shared zkVM shadow of category/core/keccak.h. Forwards keccak256(in, len,
// out) to the standardized zkVM accelerator API (c-interface-accelerators/
// zkvm_accelerators.h :: zkvm_keccak256), which both ZisK and SP1 expose as
// `extern "C"` link-time symbols (ZisK provides it natively in zisklib; SP1 in
// libzkevm.a).

#pragma once

#include <c-interface-accelerators/zkvm_accelerators.h>

#define KECCAK256_SIZE 32

#ifdef __cplusplus
extern "C"
{
#endif

#ifdef MONAD_ZKVM_ZISK
// ZisK: enter the precompile through a word-wise absorb
// (zkvm/guest/keccak_zisk.cpp). zisklib's zkvm_keccak256 assembles the sponge
// state byte by byte -- ~400-530 steps of marshalling per permutation. SP1
// keeps the accelerator shim below (its wrapper is already thin: 310
// instructions, no byte-marshalling).
void monad_zisk_keccak256(void const *in, size_t len, unsigned char out[32]);

[[gnu::always_inline]] static inline void keccak256(
    unsigned char const *const in, unsigned long const len,
    unsigned char out[KECCAK256_SIZE])
{
    monad_zisk_keccak256(in, (size_t)len, out);
}
#else
[[gnu::always_inline]] static inline void keccak256(
    unsigned char const *const in, unsigned long const len,
    unsigned char out[KECCAK256_SIZE])
{
    zkvm_keccak256(in, (size_t)len, (zkvm_keccak256_hash *)out);
}
#endif

#ifdef __cplusplus
}
#endif
