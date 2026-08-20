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

// The Keccak-f[1600] permutation that the vendored ethash sponge
// (third_party/ethash_vendor) leaves to its consumer, routed to the backend's
// Keccak precompile. Running the sponge ourselves over the raw permutation,
// rather than calling the accelerator API's zkvm_keccak256, keeps absorption
// and padding identical on both backends.
//
// This is a guest-only header, not a shadow: the host hashes via OpenSSL's
// SHA3 core (category/crypto/keccak.c) and needs no separate permutation.

#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#if defined(MONAD_ZKVM_SP1)

// SP1's syscall_keccak_permute symbol is LTO-internalised inside libzkevm.a,
// so emit the ecall the SDK itself emits: t0 = KECCAK_PERMUTE (0x00_01_01_09),
// a0 = state, a1 = 0.
[[gnu::always_inline]] static inline void monad_keccakf1600(uint64_t state[25])
{
    register uintptr_t a0 __asm__("a0") = (uintptr_t)state;
    register uintptr_t a1 __asm__("a1") = 0;
    register uint32_t t0 __asm__("t0") = 0x00010109u;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(t0), "r"(a1) : "memory");
}

#elif defined(MONAD_ZKVM_ZISK)

// ziskos's raw Keccak-f[1600] precompile entry.
void syscall_keccak_f(uint64_t state[25]);

[[gnu::always_inline]] static inline void monad_keccakf1600(uint64_t state[25])
{
    syscall_keccak_f(state);
}

#else
    #error "no zkVM backend selected: define MONAD_ZKVM_SP1 or MONAD_ZKVM_ZISK"
#endif

#ifdef __cplusplus
}
#endif
