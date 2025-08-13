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

#include <category/vm/runtime/detail.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <gtest/gtest.h>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <limits>

namespace monad::vm::compiler::test
{
    using namespace runtime;
    using namespace evmc::literals;

    class RuntimeTest : public testing::Test
    {
    protected:
        RuntimeTest();

        std::array<std::uint8_t, 128> code_;
        std::array<std::uint8_t, 128> call_data_;
        std::array<std::uint8_t, 128> call_return_data_;

        std::array<evmc_bytes32, 2> blob_hashes_;
        evmc::MockedHost host_;
        vm::runtime::Context ctx_;

        evmc_result
        success_result(std::int64_t gas_left, std::int64_t gas_refund = 0);

        evmc_result create_result(
            evmc_address prog_addr, std::int64_t gas_left,
            std::int64_t gas_refund = 0);

        evmc_result failure_result(evmc_status_code = EVMC_INTERNAL_ERROR);

        /**
         * This function performs some slightly gnarly metaprogramming to make
         * it easier for us to write unit tests for the runtime library.
         *
         * The runtime library functions are designed to take pointer arguments
         * so that the compiler can directly call them from the code generator.
         * However, this makes it irritating to unit test them, as we need to
         * pass the pointers ourselves by hand.
         *
         * This function performs a generic version of what we'd have to do by
         * hand; it takes a pack of arguments that can be converted to uint256_t
         * objects, and creates an array of the corresponding uint256_t objects
         * on the stack, which can then be passed to the runtime.
         */
        template <typename... FnArgs>
        auto wrap(void (*f)(FnArgs...))
        {
            constexpr auto use_context = detail::uses_context_v<FnArgs...>;
            constexpr auto use_result = detail::uses_result_v<FnArgs...>;
            constexpr auto use_base_gas =
                detail::uses_remaining_gas_v<FnArgs...>;

            return [f, this]<typename... Args>(Args &&...args)
                       -> std::conditional_t<
                           detail::uses_result_v<FnArgs...>,
                           uint256_t,
                           void> {
                (void)this; // Prevent compile error when `this` is not used.

                auto result = uint256_t{};

                auto uint_args = std::array<uint256_t, sizeof...(Args)>{
                    uint256_t(std::forward<Args>(args))...};

                auto arg_ptrs =
                    std::array<uint256_t const *, uint_args.size()>{};
                for (auto i = 0u; i < uint_args.size(); ++i) {
                    arg_ptrs[i] = &uint_args[i];
                }

                auto word_args = [&] {
                    if constexpr (use_result && use_context) {
                        return std::tuple_cat(
                            std::tuple(&ctx_, &result), arg_ptrs);
                    }
                    else if constexpr (use_context) {
                        return std::tuple_cat(std::tuple(&ctx_), arg_ptrs);
                    }
                    else if constexpr (use_result) {
                        return std::tuple_cat(std::tuple(&result), arg_ptrs);
                    }
                    else {
                        return arg_ptrs;
                    }
                }();

                auto all_args = [&] {
                    if constexpr (use_base_gas) {
                        return std::tuple_cat(
                            word_args, std::tuple(std::int64_t{0}));
                    }
                    else {
                        return word_args;
                    }
                }();

                std::apply(f, all_args);

                if constexpr (use_result) {
                    return result;
                }
                else {
                    return;
                }
            };
        }

        template <typename... FnArgs, typename... Args>
        auto call(void (*f)(FnArgs...), Args &&...args)
        {
            return wrap(f)(std::forward<Args>(args)...);
        }

        void set_balance(uint256_t addr, uint256_t balance);

        std::basic_string_view<uint8_t> result_data();

        void add_account_at(uint256_t addr, std::span<uint8_t> const code);
    };
}
