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

#include <category/core/bit_primitives.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstring>

namespace monad::vm::runtime
{
    // The load itself, at an offset already resolved and already covered by
    // memory.size. Split out so that the fast path and the out-of-line twin it
    // tail-calls when memory has to grow share one copy of it.
    template <Traits traits>
    [[gnu::always_inline]] inline void
    mload_at(Context *ctx, uint256_t *result_ptr, Memory::Offset const offset)
    {
#if defined(MONAD_ZKVM_SP1)
        // Same story in the load direction (~20 k per block).
        {
            uint256_t le;
            bits::copy32_to_aligned(
                reinterpret_cast<unsigned char *>(&le),
                ctx->memory.data + *offset);
            // Lane-store the swapped result: the uint256 assignment is a
            // 32-byte memcpy call on rv32 (18 k per block in the histogram).
            auto const be = bswap(le);
            auto *const d = reinterpret_cast<uint64_t *>(result_ptr);
            auto const *const sw = reinterpret_cast<uint64_t const *>(&be);
            d[0] = sw[0]; d[1] = sw[1]; d[2] = sw[2]; d[3] = sw[3];
        }
#elif defined(MONAD_ZKVM_ZISK)
        // Four loads, not a staged copy -- the mirror of mstore below.
        // `load_be_unsafe<uint256_t>` memcpys 32 bytes into a local before it
        // can byte-swap them, so gcc DMA copies EVM memory into a stack temp
        // and reads it back. Loading the words individually never takes an
        // address, so each is one `ld` and one `rev8` in registers.
        //
        // bswap reverses all 32 bytes, so the word at the lowest source
        // address becomes the result's HIGHEST word. All four are loaded
        // before any is stored, so the mapping stays readable and no store
        // can be read back.
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

    template <Traits traits>
    inline void mstore(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<32>);
#if defined(MONAD_ZKVM_SP1)
        // rv32: the 32-byte store_be staging is a memcpy CALL to unaligned EVM
        // memory (~28 k per block); swap in registers, copy inline.
        {
            auto const be = bswap(*value_ptr);
            bits::copy32_from_aligned(
                ctx->memory.data + *offset,
                reinterpret_cast<unsigned char const *>(&be));
        }
#elif defined(MONAD_ZKVM_ZISK)
        // Four stores, not a staged copy. `store_be` is `store_le(dst,
        // bswap(x))` and `store_le` takes the value's ADDRESS, so gcc has to
        // materialise the byte-swapped 32 bytes somewhere it can point at:
        // four `sd` into a 112-byte stack frame, a pointer to the temp, the
        // DMA `csrs` pair to copy it out, and the frame's own `ra` save and
        // teardown -- about 670 cells and eight steps to move bytes that were
        // already sitting in four registers.
        //
        // Writing the words one at a time never takes the value's address, so
        // it stays in registers and each word lands with one `sd`. bswap
        // reverses all 32 bytes, so word i of the result carries input word
        // 3 - i and the four go out in ascending address order -- the same 32
        // bytes `store_be` would have written, in the same places.
        {
            auto const monad_be = bswap(*value_ptr);
            auto *const monad_d = ctx->memory.data + *offset;
            store_le(monad_d, monad_be[0]);
            store_le(monad_d + 8, monad_be[1]);
            store_le(monad_d + 16, monad_be[2]);
            store_le(monad_d + 24, monad_be[3]);
        }
#else
        store_be(ctx->memory.data + *offset, *value_ptr);
#endif
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
