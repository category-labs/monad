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

#include <category/vm/runtime/types.hpp>

namespace monad::vm::runtime
{
    inline void
    mload(Context *ctx, uint256_t *result_ptr, uint256_t const *offset_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory(offset + bin<32>);
        *result_ptr = uint256_t::load_be_unsafe(ctx->memory.data + *offset);
    }

    inline void mstore(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory(offset + bin<32>);
        value_ptr->store_be(ctx->memory.data + *offset);
    }

    inline void mstore8(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory(offset + bin<1>);
        ctx->memory.data[*offset] = value_ptr->as_bytes()[0];
    }

    inline void mcopy(
        Context *ctx, uint256_t const *dst_ptr, uint256_t const *src_ptr,
        uint256_t const *size_ptr)
    {
        auto const size = ctx->get_memory_offset(*size_ptr);
        if (*size > 0) {
            auto const src = ctx->get_memory_offset(*src_ptr);
            auto const dst = ctx->get_memory_offset(*dst_ptr);
            ctx->expand_memory(max(dst, src) + size);
            auto const size_in_words = shr_ceil<5>(size);
            ctx->deduct_gas(size_in_words * bin<3>);
            std::memmove(
                ctx->memory.data + *dst, ctx->memory.data + *src, *size);
        }
    }
}
