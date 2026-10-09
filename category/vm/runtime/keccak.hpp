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
#ifdef MONAD_ZKVM_ZISK
    // A contract hashes the same 64 bytes again and again -- a mapping
    // entry's slot is keccak256(key . position), computed by every read and
    // write of the entry -- and the Keccak-f memo spares a repeat its
    // permutation but not the call around it: the handler's frame and spills,
    // the memo's copies and its compare. Such a hash is kept by its input, as
    // the EVM word it becomes, in a direct-mapped table that the SHA3 handler
    // reads (interpreter::sha3) and sha3 below fills.
    struct Sha3Memo
    {
        uint64_t in[8];
        uint256_t out;
        uint64_t filled;
        uint64_t pad[3];
    };

    static_assert(sizeof(Sha3Memo) == 128);

    inline constinit Sha3Memo sha3_memo[2048]{};

    // The entry for the 64 bytes at in, 8-aligned.
    [[gnu::always_inline]] inline Sha3Memo &
    sha3_memo_entry(uint64_t const *const in) noexcept
    {
        uint64_t const h = in[3] ^ in[7];
        return sha3_memo[(h ^ __builtin_bswap64(h)) & 2047u];
    }

    // Whether e holds the 64 bytes at in, 8-aligned: the input by the DMA
    // comparator (CSR 0x814, the length in the flag after it).
    [[gnu::always_inline]] inline bool
    sha3_memo_holds(Sha3Memo const &e, uint64_t const *const in) noexcept
    {
        uint64_t differ;
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "addi x0, %2, 64\n\t"
            ".option pop"
            : "=&r"(differ)
            : "r"(e.in),
              "r"(in),
              "m"(e.in),
              "m"(*reinterpret_cast<uint64_t const(*)[8]>(in)));
        return differ == 0 && e.filled != 0;
    }

    // Hashes the 64 bytes at in, 8-aligned, into result and the memo.
    [[gnu::always_inline]] inline void
    sha3_memo_fill(uint64_t const *const in, uint256_t *const result) noexcept
    {
        auto const hash =
            keccak256({reinterpret_cast<unsigned char const *>(in), 64});
        Sha3Memo &e = sha3_memo_entry(in);
        for (unsigned i = 0; i < 8; ++i) {
            e.in[i] = in[i];
        }
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
#ifdef MONAD_ZKVM_ZISK
        if (*size == 64 && (*offset & 7) == 0) {
            sha3_memo_fill(
                reinterpret_cast<uint64_t const *>(ctx->memory.data + *offset),
                result_ptr);
            return;
        }
#endif
        auto const hash = keccak256({ctx->memory.data + *offset, *size});
        *result_ptr = load_be<uint256_t>(hash);
    }
}
