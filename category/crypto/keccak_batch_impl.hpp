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

#pragma once

#include <category/crypto/keccak_batch.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <utility>

// Each kernel translation unit instantiates these templates for its own
// instruction set; the anonymous namespace stops the linker from folding the
// differently compiled copies into one.
//
// The AVX-512 kernel enables its instructions with a target region that opens
// after the standard headers above, not with a -m flag for the whole file. A
// standard inline function that file emits out of line is a weak symbol the
// linker may pick for the entire program, so it must stay baseline code.
#if defined(MONAD_KECCAK_BATCH_AVX512)
    #if defined(__clang__)
        #pragma clang attribute push(                                          \
            __attribute__((target("avx512f,avx512vl"))), apply_to = function)
    #else
        #pragma GCC push_options
        #pragma GCC target("avx512f,avx512vl")
    #endif
#endif

namespace
{

    using u64x4 = uint64_t __attribute__((vector_size(32)));
    using u64x8 = uint64_t __attribute__((vector_size(64)));

    constexpr size_t keccak256_rate = 136; // bytes absorbed per permutation
    constexpr size_t keccak256_rate_words = keccak256_rate / sizeof(uint64_t);

    constexpr std::array<uint64_t, 24> keccak_round_constants = {
        0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
        0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
        0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
        0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
        0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
        0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
        0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
        0x8000000000008080, 0x0000000080000001, 0x8000000080008008};

    // Indexed by lane x + 5y.
    constexpr std::array<int, 25> keccak_rho = {
        0,  1,  62, 28, 27, 36, 44, 6,  55, 20, 3,  10, 43,
        25, 39, 41, 45, 15, 21, 8,  18, 2,  61, 56, 14};

    // Pi: A'[x, y] = A[(x + 3y) mod 5, x].
    consteval size_t pi_source(size_t const x, size_t const y)
    {
        return (x + 3 * y) % 5 + 5 * x;
    }

    template <int n, typename V>
    [[gnu::always_inline]] inline V rotl(V const v)
    {
        if constexpr (n == 0) {
            return v;
        }
        else {
            return (v << n) | (v >> (64 - n));
        }
    }

    template <size_t y, typename V>
    [[gnu::always_inline]] inline void
    rho_pi_chi_row(V const (&a)[25], V const (&d)[5], V (&e)[25])
    {
        [&]<size_t... x>(
            std::index_sequence<x...>) __attribute__((always_inline)) {
            V const b[5] = {rotl<keccak_rho[pi_source(x, y)]>(
                a[pi_source(x, y)] ^ d[pi_source(x, y) % 5])...};
            ((e[x + 5 * y] = b[x] ^ (~b[(x + 1) % 5] & b[(x + 2) % 5])), ...);
        }(std::make_index_sequence<5>{});
    }

    template <typename V>
    [[gnu::always_inline]] inline void
    keccak_round(V const (&a)[25], V (&e)[25], uint64_t const rc)
    {
        V c[5];
        V d[5];
        [&]<size_t... x>(
            std::index_sequence<x...>) __attribute__((always_inline)) {
            ((c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]), ...);
            ((d[x] = c[(x + 4) % 5] ^ rotl<1>(c[(x + 1) % 5])), ...);
        }(std::make_index_sequence<5>{});
        [&]<size_t... y>(std::index_sequence<y...>)
            __attribute__((always_inline)) {
                (rho_pi_chi_row<y>(a, d, e), ...);
            }(std::make_index_sequence<5>{});
        e[0] ^= rc;
    }

    template <typename V>
    [[gnu::always_inline]] inline void keccak_f1600(V (&a)[25])
    {
        V e[25];
        for (size_t i = 0; i < keccak_round_constants.size(); i += 2) {
            keccak_round(a, e, keccak_round_constants[i]);
            keccak_round(e, a, keccak_round_constants[i + 1]);
        }
    }

    template <typename V>
    constexpr size_t lane_count = sizeof(V) / sizeof(uint64_t);

    // Hashes exactly lane_count<V> jobs.
    template <typename V>
    void keccak256_lanes(monad_keccak256_job const *const jobs)
    {
        constexpr size_t lanes = lane_count<V>;
        static constexpr uint8_t zero_block[keccak256_rate] = {};

        alignas(64) uint8_t last_block[lanes][keccak256_rate];
        size_t full_blocks[lanes];
        size_t total_blocks = 0;
        for (size_t i = 0; i < lanes; ++i) {
            size_t const len = jobs[i].len;
            size_t const rem = len % keccak256_rate;
            full_blocks[i] = len / keccak256_rate;
            if (rem > 0) {
                std::memcpy(last_block[i], jobs[i].in + len - rem, rem);
            }
            std::memset(last_block[i] + rem, 0, keccak256_rate - rem);
            last_block[i][rem] = 0x01;
            last_block[i][keccak256_rate - 1] |= 0x80;
            total_blocks = std::max(total_blocks, full_blocks[i] + 1);
        }

        V a[25] = {};
        for (size_t block = 0; block < total_blocks; ++block) {
            uint8_t const *src[lanes];
            for (size_t i = 0; i < lanes; ++i) {
                src[i] = block < full_blocks[i]
                             ? jobs[i].in + block * keccak256_rate
                             : (block == full_blocks[i] ? last_block[i]
                                                        : zero_block);
            }
#pragma GCC unroll 17
            for (size_t w = 0; w < keccak256_rate_words; ++w) {
                V word = {};
                for (size_t i = 0; i < lanes; ++i) {
                    uint64_t x;
                    std::memcpy(&x, src[i] + 8 * w, sizeof(x));
                    word[i] = x;
                }
                a[w] ^= word;
            }
            keccak_f1600(a);
            // A lane's digest is stored only after its whole input has been
            // read, which is what lets out alias in.
            for (size_t i = 0; i < lanes; ++i) {
                if (block == full_blocks[i]) {
#pragma GCC unroll 4
                    for (size_t w = 0; w < 4; ++w) {
                        uint64_t const x = a[w][i];
                        std::memcpy(jobs[i].out + 8 * w, &x, sizeof(x));
                    }
                }
            }
        }
    }

    // Hashes 1 <= count <= lane_count<V> jobs, filling idle lanes with copies
    // of the first job so the group costs no extra permutations.
    template <typename V>
    void
    keccak256_partial(monad_keccak256_job const *const jobs, size_t const count)
    {
        constexpr size_t lanes = lane_count<V>;
        uint8_t discard[lanes][32];
        monad_keccak256_job padded[lanes];
        for (size_t i = 0; i < lanes; ++i) {
            padded[i] = i < count ? jobs[i]
                                  : monad_keccak256_job{
                                        .in = jobs[0].in,
                                        .len = jobs[0].len,
                                        .out = discard[i]};
        }
        keccak256_lanes<V>(padded);
    }

}

#if defined(MONAD_KECCAK_BATCH_AVX512)
    #if defined(__clang__)
        #pragma clang attribute pop
    #else
        #pragma GCC pop_options
    #endif
#endif
