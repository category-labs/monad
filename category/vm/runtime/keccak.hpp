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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

#include <ethash/keccak.hpp>

namespace monad::vm::runtime
{
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

        auto const hash = ethash::keccak256(ctx->memory.data + *offset, *size);
        *result_ptr = uint256_t::load_be(hash.bytes);
    }
}
