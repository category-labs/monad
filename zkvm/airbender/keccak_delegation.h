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

#pragma once

// Airbender's Keccak-f delegation (zksync-airbender common_constants
// delegation_types/keccak_f1600.rs): 361 CSR writes over a 256-byte-aligned
// block whose slots 0..24 hold the lanes in the standard x + 5y order and
// 25..29 the column parities. Per round, five column-parity (0x7cd), five
// theta/rho (0x7cc) and five chi (0x7ce) calls; a last column-parity call
// applies the delayed final iota. x10 starts at zero and the circuit steps
// it; x11 points at the block. The run must be one uninterrupted sequence,
// which the transpiler recognises by its first CSR and its length.
//
// Shared by the runtime (runtime.c), which defines the block, and the sponge
// (zkvm/guest/keccak_accel.cpp), which absorbs into the block and runs the
// sequence inline: a call per permutation, about a hundred thousand a block,
// costs more than the sequence's own setup.

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// The delegation's block, 256-byte aligned where runtime.c defines it.
extern uint64_t monad_zkvm_airbender_keccak_block[32];

#ifdef __cplusplus
}
#endif

#define MONAD_ZKVM_AIRBENDER_KECCAK_CALL(csr) "csrrw x0, " #csr ", x0\n\t"
#define MONAD_ZKVM_AIRBENDER_KECCAK_5(csr)                                     \
    MONAD_ZKVM_AIRBENDER_KECCAK_CALL(csr)                                      \
    MONAD_ZKVM_AIRBENDER_KECCAK_CALL(csr)                                      \
    MONAD_ZKVM_AIRBENDER_KECCAK_CALL(csr)                                      \
    MONAD_ZKVM_AIRBENDER_KECCAK_CALL(csr)                                      \
    MONAD_ZKVM_AIRBENDER_KECCAK_CALL(csr)
#define MONAD_ZKVM_AIRBENDER_KECCAK_ROUND                                      \
    MONAD_ZKVM_AIRBENDER_KECCAK_5(0x7cd)                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_5(0x7cc)                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_5(0x7ce)
#define MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS                                   \
    MONAD_ZKVM_AIRBENDER_KECCAK_ROUND                                          \
    MONAD_ZKVM_AIRBENDER_KECCAK_ROUND                                          \
    MONAD_ZKVM_AIRBENDER_KECCAK_ROUND                                          \
    MONAD_ZKVM_AIRBENDER_KECCAK_ROUND
#define MONAD_ZKVM_AIRBENDER_KECCAK_24_ROUNDS                                  \
    MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS                                       \
    MONAD_ZKVM_AIRBENDER_KECCAK_4_ROUNDS

// Keccak-f over the block, in place. The clobber orders the lanes' stores
// before the sequence and their loads after it.
static inline __attribute__((always_inline)) void
monad_zkvm_airbender_keccak_block_permute(void)
{
    __asm__ volatile("mv x11, %0\n\t"
                     "add x10, x0, x0\n\t" MONAD_ZKVM_AIRBENDER_KECCAK_24_ROUNDS
                         MONAD_ZKVM_AIRBENDER_KECCAK_CALL(0x7cd)
                     :
                     : "r"(monad_zkvm_airbender_keccak_block)
                     : "x10", "x11", "memory");
}
