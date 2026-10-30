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
// permutations cannot repeat -- see the entry point's own comment for which
// callers those are and why not filing is sound. It has no host counterpart,
// so callers name it directly rather than through a shadowed name.
extern "C" void monad_zkvm_keccak256_fast_nomemo(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

// The same digest with the memo on the first `memo_blocks` rate blocks only,
// for a bytecode that shares that prefix with another.
extern "C" void monad_zkvm_keccak256_fast_memo_prefix(
    void const *in, size_t len, size_t memo_blocks,
    uint8_t out[KECCAK256_SIZE]);

// A trie node's digest, the pre-state check's and the post-state's: the memo
// files all of the former's permutations but the last and none of the latter's
// (zkvm/guest/keccak_accel.cpp, Filing).
extern "C" void monad_zkvm_keccak256_trie_prime(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);
extern "C" void monad_zkvm_keccak256_trie_patch(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

#if defined(MONAD_ZKVM_ZISK)
// The same digest for the lengths callers most often pass as constants: an
// address, a key or a slot, a public key. Each asks the known-input table at
// its length and otherwise builds its one padded block with the length folded
// in; see keccak256_one_block_n in zkvm/guest/keccak_accel.cpp.
extern "C" void monad_zkvm_keccak256_20(
    void const *in, uint8_t out[KECCAK256_SIZE]);
extern "C" void monad_zkvm_keccak256_32(
    void const *in, uint8_t out[KECCAK256_SIZE]);
extern "C" void monad_zkvm_keccak256_64(
    void const *in, uint8_t out[KECCAK256_SIZE]);
#endif

#if defined(MONAD_ZKVM_ZISK) &&                                                \
    (!defined(MONAD_ZKVM_KECCAKF_MEMO) || MONAD_ZKVM_KECCAKF_MEMO)
    #define MONAD_ZKVM_KECCAKF_RESUME 1

constexpr size_t KECCAK256_RATE = 136;

// monad_zkvm_keccak256_trie_prime of an input of at least KECCAK256_RATE
// bytes, which also leaves in `*mark` where it kept the states after its whole
// blocks, or zero when it kept none.
extern "C" void monad_zkvm_keccak256_trie_prime_mark(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE], uint64_t *mark);

// monad_zkvm_keccak256_trie_patch of an input whose first `blocks` rate
// blocks (at least one, and fewer than the input holds) are the bytes an
// earlier prime absorbed when it left `mark`: it starts from the state the
// prime kept after them, or, when the mark is zero, from the input's start.
extern "C" void monad_zkvm_keccak256_trie_resume(
    void const *in, size_t len, uint8_t out[KECCAK256_SIZE], uint64_t mark,
    size_t blocks);
#endif

[[gnu::always_inline]] static inline void monad_keccak256(
    void const *const in, size_t const len, uint8_t out[KECCAK256_SIZE])
{
#if defined(MONAD_ZKVM_ZISK)
    // gcc settles __builtin_constant_p only after inlining, so this sees the
    // length of the caller the wrapper ends up in. A site where it does not
    // fold keeps the general entry, which computes the same digest.
    if (__builtin_constant_p(len)) {
        if (len == 32) {
            monad_zkvm_keccak256_32(in, out);
            return;
        }
        if (len == 20) {
            monad_zkvm_keccak256_20(in, out);
            return;
        }
        if (len == 64) {
            monad_zkvm_keccak256_64(in, out);
            return;
        }
    }
#endif
    monad_zkvm_keccak256_fast(in, len, out);
}
