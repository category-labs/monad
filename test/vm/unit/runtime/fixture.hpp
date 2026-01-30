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
#include <category/vm/runtime/detail.hpp>
#include <category/vm/runtime/types.hpp>
#include <monad/test/traits_test.hpp>
#include <test/vm/utils/test_context.hpp>

#include <gtest/gtest.h>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <limits>

extern "C" void tests_trampoline(void *, void (*)(void *), void *);

namespace monad::vm::compiler::test
{
    using namespace runtime;
    using namespace evmc::literals;

    class RuntimeTestBase
    {
    protected:
        RuntimeTestBase();

        std::array<std::uint8_t, 128> code_;
        std::array<std::uint8_t, 128> call_data_;
        std::array<std::uint8_t, 128> call_return_data_;

        std::array<evmc_bytes32, 2> blob_hashes_;
        evmc::MockedHost host_;
        monad::vm::test::TestContext test_ctx_;
        vm::runtime::Context &ctx_;

        evmc_result
        success_result(std::int64_t gas_left, std::int64_t gas_refund = 0);

        evmc_result create_result(
            evmc_address prog_addr, std::int64_t gas_left,
            std::int64_t gas_refund = 0);

        evmc_result failure_result(evmc_status_code = EVMC_INTERNAL_ERROR);

        // shim to be able to pass a function pointer to tests_trampoline
        // which will then correctly invoke the actual closure/lambda
        template <typename Closure>
        static void call_closure(void *ptr)
        {
            auto *fn = reinterpret_cast<Closure *>(ptr);
            (*fn)();
        }

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

                // if f uses the context, it may exit early by calling
                // ctx->exit(...) therefore, have to call it via the
                // tests_trampoline to set up the compiler calling convention
                // and if f returns, call ctx_->exit(StatusCode::Success) to
                // restore the previous context correctly
                if constexpr (use_context) {
                    auto f_lambda = [f, &all_args]() {
                        std::apply(f, all_args);
                        std::get<0>(all_args)->exit(StatusCode::Success);
                    };

                    tests_trampoline(
                        static_cast<void *>(&ctx_.exit_stack_ptr),
                        &call_closure<decltype(f_lambda)>,
                        static_cast<void *>(&f_lambda));
                }
                else {
                    std::apply(f, all_args);
                }

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

    class RuntimeTest
        : public RuntimeTestBase
        , public testing::Test
    {
    };

    template <typename T>
    class RuntimeTraitsTest
        : public RuntimeTestBase
        , public TraitsTest<T>
    {
    public:
        static constexpr runtime::Memory::Version get_memory_version()
        {
            return TraitsTest<T>::Trait::mip_3_active()
                       ? runtime::Memory::Version::MIP3
                       : runtime::Memory::Version::V1;
        }

        void assert_delegated(evmc::address const &delegate_addr)
        {
            ASSERT_EQ(ctx_.result.status, StatusCode::Success);

            ASSERT_EQ(host_.recorded_calls.size(), 1);

            if constexpr (TraitsTest<T>::Trait::evm_rev() >= EVMC_PRAGUE) {
                ASSERT_EQ(
                    host_.access_account(delegate_addr), EVMC_ACCESS_WARM);
                ASSERT_EQ(
                    host_.recorded_calls[0].flags &
                        static_cast<uint32_t>(EVMC_DELEGATED),
                    static_cast<uint32_t>(EVMC_DELEGATED));
            }
            else {
                ASSERT_EQ(
                    host_.access_account(delegate_addr), EVMC_ACCESS_COLD);
                ASSERT_NE(
                    host_.recorded_calls[0].flags &
                        static_cast<uint32_t>(EVMC_DELEGATED),
                    static_cast<uint32_t>(EVMC_DELEGATED));
            }
        }
    };
}

DEFINE_TRAITS_FIXTURE(RuntimeTraitsTest);
