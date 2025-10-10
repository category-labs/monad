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

#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/detail.hpp>
#include <category/vm/runtime/types.hpp>

namespace monad::vm::interpreter
{
    template <typename... FnArgs>
    [[gnu::always_inline]]
    inline void call_runtime(
        void (*f)(FnArgs...), runtime::Context &ctx,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining)
    {
        constexpr auto use_context = runtime::detail::uses_context_v<FnArgs...>;
        constexpr auto use_result = runtime::detail::uses_result_v<FnArgs...>;
        constexpr auto use_base_gas =
            runtime::detail::uses_remaining_gas_v<FnArgs...>;

        constexpr auto stack_arg_count =
            sizeof...(FnArgs) -
            std::ranges::count(
                std::array{use_context, use_result, use_base_gas}, true);

        auto const stack_args =
            [&]<std::size_t... Is>(std::index_sequence<Is...>) {
                return std::tuple{(stack_top - Is)...};
            }(std::make_index_sequence<stack_arg_count>());

        auto const with_result_args = [&] {
            if constexpr (use_result) {
                if constexpr (stack_arg_count == 0) {
                    return std::tuple(stack_top + 1);
                }
                else {
                    return std::tuple_cat(
                        std::tuple(std::get<stack_arg_count - 1>(stack_args)),
                        stack_args);
                }
            }
            else {
                return stack_args;
            }
        }();

        auto const with_context_args = [&] {
            if constexpr (use_context) {
                return std::tuple_cat(std::tuple(&ctx), with_result_args);
            }
            else {
                return with_result_args;
            }
        }();

        auto const all_args = [&] {
            if constexpr (use_base_gas) {
                return std::tuple_cat(
                    with_context_args, std::tuple(std::int64_t{0}));
            }
            else {
                return with_context_args;
            }
        }();

        ctx.gas_remaining = gas_remaining;
        std::apply(f, all_args);

        static_assert(
            stack_arg_count <= std::numeric_limits<std::ptrdiff_t>::max());
        gas_remaining = ctx.gas_remaining;
    }
}
