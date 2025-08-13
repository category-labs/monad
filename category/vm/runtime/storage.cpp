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

#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <cstdint>

#ifdef MONAD_COMPILER_TESTING
    #include <category/vm/runtime/transmute.hpp>
#else
    #include <exception>
#endif

namespace monad::vm::runtime
{
#ifdef MONAD_COMPILER_TESTING
    bool debug_tstore_stack(
        Context const *ctx, uint256_t const *stack, uint64_t stack_size,
        uint64_t offset, uint64_t base_offset)
    {
        auto const magic = uint256_t{0xdeb009};
        auto const base = (magic + base_offset) * 1024;
        if (offset == 0) {
            auto const base_key = bytes32_from_uint256(base);
            auto const base_value = ctx->host->get_transient_storage(
                ctx->context, &ctx->env.recipient, &base_key);
            if (base_value != evmc::bytes32{}) {
                // If this transient storage location has already been written,
                // then we are likely in a loop. We return early in this case
                // to avoid repeatedly saving stack to transient storage.
                return false;
            }
        }
        for (uint64_t i = 0; i < stack_size; ++i) {
            auto const key = bytes32_from_uint256(base + i + offset);
            auto const &x = stack[static_cast<int64_t>(-i) - 1];
            // Make sure we do not store zero, because incorrect non-zero is
            // more likely to be noticed, due to zero being the default:
            auto const s = x < magic ? x + 1 : x;
            auto const value = bytes32_from_uint256(s);
            ctx->host->set_transient_storage(
                ctx->context, &ctx->env.recipient, &key, &value);
        }
        return true;
    }
#else
    bool debug_tstore_stack(
        Context const *, uint256_t const *, uint64_t, uint64_t, uint64_t)
    {
        std::terminate();
    }
#endif
}
