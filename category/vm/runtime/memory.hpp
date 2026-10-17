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
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstring>

namespace monad::vm::runtime
{
#if defined(MONAD_ZKVM_AIRBENDER)
    // A big-endian 32-byte word at a 4-aligned address, by eight loads and
    // rev8s, where load_be_unsafe stages it through a 32-byte memcpy call and
    // swaps it after. A limb at a time, each stored before the next is read:
    // the source is never the stack, and with eight words live at once a
    // handler runs out of registers and saves some to a frame.
    [[gnu::always_inline]] inline void
    load_be32_aligned4(uint256_t *const result_ptr, uint8_t const *const p)
    {
        auto const *const a =
            static_cast<uint8_t const *>(__builtin_assume_aligned(p, 4));
    #pragma GCC unroll 4
        for (std::size_t k = 0; k < 4; ++k) {
            uint32_t hi;
            uint32_t lo;
            __builtin_memcpy(&hi, a + 24 - 8 * k, 4);
            __builtin_memcpy(&lo, a + 28 - 8 * k, 4);
            (*result_ptr)[k] = (uint64_t{::monad::bit::byteswap(hi)} << 32) |
                               ::monad::bit::byteswap(lo);
        }
    }

    // The same store, the destination never the stack.
    [[gnu::always_inline]] inline void
    store_be32_aligned4(uint8_t *const p, uint256_t const *const value_ptr)
    {
        auto *const a = static_cast<uint8_t *>(__builtin_assume_aligned(p, 4));
    #pragma GCC unroll 4
        for (std::size_t k = 0; k < 4; ++k) {
            uint64_t const limb = (*value_ptr)[k];
            uint32_t const lo =
                ::monad::bit::byteswap(static_cast<uint32_t>(limb));
            uint32_t const hi =
                ::monad::bit::byteswap(static_cast<uint32_t>(limb >> 32));
            __builtin_memcpy(a + 28 - 8 * k, &lo, 4);
            __builtin_memcpy(a + 24 - 8 * k, &hi, 4);
        }
    }
#endif

    // Load 32 bytes at a validated offset; [offset, offset + 32) must already
    // be within memory.size.
    template <Traits traits>
    [[gnu::always_inline]] inline void
    mload_at(Context *ctx, uint256_t *result_ptr, Memory::Offset const offset)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Load four words directly to avoid a 32-byte DMA copy to the stack.
        // Big-endian order puts the first word in the highest result limb.
        // Read all words before writing, in case input and result overlap.
        {
            auto const *const monad_s = ctx->memory.data + *offset;
            auto const monad_w3 = load_be_unsafe<uint64_t>(monad_s);
            auto const monad_w2 = load_be_unsafe<uint64_t>(monad_s + 8);
            auto const monad_w1 = load_be_unsafe<uint64_t>(monad_s + 16);
            auto const monad_w0 = load_be_unsafe<uint64_t>(monad_s + 24);
            (*result_ptr)[0] = monad_w0;
            (*result_ptr)[1] = monad_w1;
            (*result_ptr)[2] = monad_w2;
            (*result_ptr)[3] = monad_w3;
        }
#elif defined(MONAD_ZKVM_AIRBENDER)
        // A 4-aligned word, nearly every MLOAD, without the memcpy call.
        auto const *const monad_s = ctx->memory.data + *offset;
        if ((reinterpret_cast<std::uintptr_t>(monad_s) & 3) == 0) {
            load_be32_aligned4(result_ptr, monad_s);
        }
        else {
            *result_ptr = load_be_unsafe<uint256_t>(monad_s);
        }
#else
        *result_ptr = load_be_unsafe<uint256_t>(ctx->memory.data + *offset);
#endif
    }

    template <Traits traits>
    inline void
    mload(Context *ctx, uint256_t *result_ptr, uint256_t const *offset_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<32>);
        mload_at<traits>(ctx, result_ptr, offset);
    }

    // Store 32 bytes at a validated offset; [offset, offset + 32) must already
    // be within memory.size.
    template <Traits traits>
    [[gnu::always_inline]] inline void mstore_at(
        Context *ctx, Memory::Offset const offset, uint256_t const *value_ptr)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Store one byte-swapped word at a time to avoid staging a 32-byte
        // temporary on the stack for a DMA copy. The resulting bytes match
        // store_be.
        {
            auto const monad_be = bswap(*value_ptr);
            auto *const monad_d = ctx->memory.data + *offset;
            store_le(monad_d, monad_be[0]);
            store_le(monad_d + 8, monad_be[1]);
            store_le(monad_d + 16, monad_be[2]);
            store_le(monad_d + 24, monad_be[3]);
        }
#elif defined(MONAD_ZKVM_AIRBENDER)
        // The same for MSTORE.
        auto *const monad_d = ctx->memory.data + *offset;
        if ((reinterpret_cast<std::uintptr_t>(monad_d) & 3) == 0) {
            store_be32_aligned4(monad_d, value_ptr);
        }
        else {
            store_be(monad_d, *value_ptr);
        }
#else
        store_be(ctx->memory.data + *offset, *value_ptr);
#endif
    }

    template <Traits traits>
    inline void mstore(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<32>);
        mstore_at<traits>(ctx, offset, value_ptr);
    }

    template <Traits traits>
    inline void mstore8(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<1>);
        ctx->memory.data[*offset] = as_bytes(*value_ptr)[0];
    }

    template <Traits traits>
#if defined(MONAD_ZKVM_ZISK)
    // Called on ZisK: inlined, its memory growth, which keeps
    // memory_access32_end too, would not fit MCOPY's handler slot.
    [[gnu::noinline]]
#endif
    inline void mcopy(
        Context *ctx, uint256_t const *dst_ptr, uint256_t const *src_ptr,
        uint256_t const *size_ptr)
    {
        auto const size = ctx->get_memory_offset(*size_ptr);
        if (*size > 0) {
            auto const src = ctx->get_memory_offset(*src_ptr);
            auto const dst = ctx->get_memory_offset(*dst_ptr);
            ctx->expand_memory<traits>(max(dst, src) + size);
            auto const size_in_words = shr_ceil<5>(size);
            ctx->deduct_gas(size_in_words * bin<3>);
            std::memmove(
                ctx->memory.data + *dst, ctx->memory.data + *src, *size);
        }
    }
}
