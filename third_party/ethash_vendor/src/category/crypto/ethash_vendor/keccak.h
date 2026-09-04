// ethash: C/C++ implementation of Ethash, the Ethereum Proof of Work algorithm.
// Copyright 2018 Pawel Bylica.
// SPDX-License-Identifier: Apache-2.0
//
// Vendored from ethash's lib/keccak/keccak.c, reduced to the sponge and
// specialised to a 256-bit digest. The Keccak-f[1600] permutation is not
// included; monad_keccakf1600() is supplied by the consumer. See ../NOTICE
// for the full list of divergences from upstream.

#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// The sponge below calls the Keccak-f[1600] permutation
///
///     void monad_keccakf1600(uint64_t state[25]);
///
/// which permutes the 25 64-bit words of state in place. It is neither
/// declared nor defined here: the consumer must supply it before including
/// this header, so that a target with a native Keccak primitive can use it
/// instead of a software round function, and can supply it inline rather than
/// as a link-time symbol. The zkVM guest routes it to the backend's Keccak
/// precompile in zkvm/category/crypto/keccakf1600.h.

[[gnu::always_inline]] static inline uint64_t monad_keccak_to_le64(uint64_t const word)
{
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    return __builtin_bswap64(word);
#else
    return word;
#endif
}

/// Loads 64-bit integer from given memory location as little-endian number.
[[gnu::always_inline]] static inline uint64_t monad_keccak_load_le(uint8_t const *const data)
{
    /* memcpy is the best way of expressing the intention. Every compiler will
       optimize is to single load instruction if the target architecture
       supports unaligned memory access (GCC and clang even in O0).
       This is great trick because we are violating C/C++ memory alignment
       restrictions with no performance penalty. */
    uint64_t word;
    __builtin_memcpy(&word, data, sizeof(word));
    return monad_keccak_to_le64(word);
}

/// Computes the Keccak-256 hash of the given input.
///
/// Defined here rather than in a translation unit, and always_inline, because
/// the guest's hottest hashes take a compile-time-constant length (the trie
/// keys, keccak256(addr.bytes) / keccak256(slot.bytes)). Inlined, the block
/// loop, the word loop and the byte tail all fold away at those call sites.
///
/// @param out  The 32-byte digest. Has no alignment requirement.
[[gnu::always_inline]] static inline void monad_keccak256(
    void const *const in, size_t size, uint8_t out[32])
{
    static size_t const word_size = sizeof(uint64_t);
    static size_t const block_size = (1600 - 256 * 2) / 8;

    size_t i;
    uint8_t const *data = (uint8_t const *)in;
    uint64_t *state_iter;
    uint64_t last_word = 0;
    uint8_t *last_word_iter = (uint8_t *)&last_word;

    uint64_t state[25] = {0};

    while (size >= block_size) {
        for (i = 0; i < (block_size / word_size); ++i) {
            state[i] ^= monad_keccak_load_le(data);
            data += word_size;
        }

        monad_keccakf1600(state);

        size -= block_size;
    }

    state_iter = state;

    while (size >= word_size) {
        *state_iter ^= monad_keccak_load_le(data);
        ++state_iter;
        data += word_size;
        size -= word_size;
    }

    while (size > 0) {
        *last_word_iter = *data;
        ++last_word_iter;
        ++data;
        --size;
    }
    *last_word_iter = 0x01;
    *state_iter ^= monad_keccak_to_le64(last_word);

    state[(block_size / word_size) - 1] ^= 0x8000000000000000;

    monad_keccakf1600(state);

    for (i = 0; i < (32 / word_size); ++i) {
        uint64_t const word = monad_keccak_to_le64(state[i]);
        __builtin_memcpy(out + i * word_size, &word, word_size);
    }
}

#ifdef __cplusplus
}
#endif
