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

#include "category/core/runtime/uint256.hpp"
#include "category/vm/evm/traits.hpp"
#include "category/vm/runtime/bin.hpp"
#include "category/vm/runtime/types.hpp"
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/runtime/memory.hpp>
#include <cstring>

namespace monad::vm::runtime
{
    template <Traits traits>
    void mload(Context *ctx, uint256_t *result_ptr, uint256_t const *offset_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<32>);
        *result_ptr = uint256_t::load_be_unsafe(ctx->memory.data + *offset);
    }

    EXPLICIT_TRAITS(mload);

    template <Traits traits>
    void mstore(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<32>);
        value_ptr->store_be(ctx->memory.data + *offset);
    }

    EXPLICIT_TRAITS(mstore);

    template <Traits traits>
    void mstore8(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto const offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory<traits>(offset + bin<1>);
        ctx->memory.data[*offset] = value_ptr->as_bytes()[0];
    }

    EXPLICIT_TRAITS(mstore8);

    template <Traits traits>
    void mcopy(
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

    EXPLICIT_TRAITS(mcopy);
}
