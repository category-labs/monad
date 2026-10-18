// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/types.hpp>

#ifdef MONAD_ZKVM_KECCAK_SITES
#include <category/core/keccak_sites.hpp>
#else
#define MONAD_KECCAK_SITE(s, len) ((void)0)
#endif

namespace monad::vm::runtime
{
#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_AIRBENDER)
    // A contract hashes the same 64 bytes again and again -- a mapping
    // entry's slot is keccak256(key . position), computed by every read and
    // write of the entry -- and the same 32 -- a dynamic array's data starts
    // at keccak256(position) -- and the Keccak-f memo spares a repeat its
    // permutation but not the call around it: the handler's frame and spills,
    // the memo's copies and its compare. Such a hash is kept by its input, as
    // the EVM word it becomes, in a direct-mapped table per size that the
    // SHA3 handler reads (interpreter::sha3) and sha3 below fills.
    template <size_t N>
    struct Sha3Memo
    {
        uint64_t in[N / 8];
        uint256_t out;
        uint64_t filled;
        uint64_t pad[(128 - N - 40) / 8];
    };

    static_assert(sizeof(Sha3Memo<64>) == 128);
    static_assert(sizeof(Sha3Memo<32>) == 128);

    inline constinit Sha3Memo<64> sha3_memo64[2048]{};
    inline constinit Sha3Memo<32> sha3_memo32[1024]{};

    // The entry for the N bytes at in, 8-aligned.
    template <size_t N>
    [[gnu::always_inline]] inline Sha3Memo<N> &
    sha3_memo_entry(uint64_t const *const in) noexcept
    {
    #if defined(MONAD_ZKVM_AIRBENDER)
        // From the last 32-bit words of the key and of the slot number, on
        // rv32, where a 64-bit byte swap is a call.
        auto const *const w = reinterpret_cast<uint32_t const *>(in);
        if constexpr (N == 64) {
            uint32_t const h = w[7] ^ w[15] ^ w[6];
            return sha3_memo64[(h ^ (h >> 11) ^ (h >> 22)) & 2047u];
        }
        else {
            static_assert(N == 32);
            uint32_t const h = w[7] ^ w[6];
            return sha3_memo32[(h ^ (h >> 10) ^ (h >> 20)) & 1023u];
        }
    #else
        if constexpr (N == 64) {
            uint64_t const h = in[3] ^ in[7];
            return sha3_memo64[(h ^ __builtin_bswap64(h)) & 2047u];
        }
        else {
            static_assert(N == 32);
            uint64_t const h = in[3];
            return sha3_memo32[(h ^ __builtin_bswap64(h)) & 1023u];
        }
    #endif
    }

    // Whether e holds the N bytes at in, 8-aligned: the input by the DMA
    // comparator (CSR 0x814, the length in the flag after it).
    template <size_t N>
    [[gnu::always_inline]] inline bool
    sha3_memo_holds(Sha3Memo<N> const &e, uint64_t const *const in) noexcept
    {
    #if defined(MONAD_ZKVM_AIRBENDER)
        // By 32-bit words, both sides word-aligned: the last first, which
        // tells most inputs apart.
        auto const *const a = reinterpret_cast<uint32_t const *>(e.in);
        auto const *const b = reinterpret_cast<uint32_t const *>(in);
        if (a[N / 4 - 1] != b[N / 4 - 1] || e.filled == 0) {
            return false;
        }
        uint32_t differ = 0;
        #pragma GCC unroll 16
        for (size_t i = 0; i < N / 4 - 1; ++i) {
            differ |= a[i] ^ b[i];
        }
        return differ == 0;
    #else
        uint64_t differ;
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "addi x0, %2, %5\n\t"
            ".option pop"
            : "=&r"(differ)
            : "r"(e.in),
              "r"(in),
              "m"(e.in),
              "m"(*reinterpret_cast<uint64_t const(*)[N / 8]>(in)),
              "i"(N));
        return differ == 0 && e.filled != 0;
    #endif
    }

    // Hashes the N bytes at in, 8-aligned, into result and the memo.
    template <size_t N>
    [[gnu::always_inline]] inline void
    sha3_memo_fill(uint64_t const *const in, uint256_t *const result) noexcept
    {
        auto const hash =
            keccak256({reinterpret_cast<unsigned char const *>(in), N});
        Sha3Memo<N> &e = sha3_memo_entry<N>(in);
        __builtin_memcpy(e.in, in, N);
        e.out = load_be<uint256_t>(hash);
        e.filled = 1;
        *result = e.out;
    }

#endif
    template <Traits traits>
    inline void sha3(
        Context *ctx, uint256_t *result_ptr, uint256_t const *offset_ptr,
        uint256_t const *size_ptr)
    {
        Memory::Offset offset;
        auto const size = ctx->get_memory_offset(*size_ptr);

        if (*size > 0) {
            offset = ctx->get_memory_offset(*offset_ptr);

            ctx->expand_memory<traits>(offset + size);

            auto const word_size = shr_ceil<5>(size);
            ctx->deduct_gas(word_size * bin<6>);
        }

        MONAD_KECCAK_SITE(SHA3_OPCODE, *size);
#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_AIRBENDER)
        if ((*size == 64 || *size == 32) && (*offset & 7) == 0) {
            auto const *const in =
                reinterpret_cast<uint64_t const *>(ctx->memory.data + *offset);
            if (*size == 64) {
                sha3_memo_fill<64>(in, result_ptr);
            }
            else {
                sha3_memo_fill<32>(in, result_ptr);
            }
            return;
        }
#endif
        auto const hash = keccak256({ctx->memory.data + *offset, *size});
        *result_ptr = load_be<uint256_t>(hash);
    }
}
