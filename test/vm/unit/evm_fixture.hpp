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

#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <evmone/baseline.hpp>
#include <evmone/constants.hpp>
#include <evmone/evmone.h>
#include <evmone/vm.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <span>

namespace fs = std::filesystem;

namespace monad::vm::compiler::test
{
    template <typename T>
    class VMTraitsTestBase
    {
    public:
        VMTraitsTestBase() noexcept = default;

    protected:
        enum Implementation
        {
            Compiler,
            Interpreter,
            Evmone,
        };

        static constexpr auto get_trait()
        {
            if constexpr (std::
                              same_as<typename T::value_type, monad_revision>) {
                return monad::MonadTraits<T::value>{};
            }
            else {
                return monad::EvmTraits<T::value>{};
            }
        }

        using Trait = decltype(get_trait());

        static consteval bool is_monad_trait() noexcept
        {
            return monad::is_monad_trait_v<Trait>;
        }

        static consteval bool is_evm_trait() noexcept
        {
            return monad::is_evm_trait_v<Trait>;
        }

        monad::vm::VM vm_{};

        evmc_message msg_{};

        evmc::MockedHost host_;

        evmc::Result result_;

        std::span<uint8_t const> output_data_{};

        void pre_execute(
            std::int64_t gas_limit,
            std::span<std::uint8_t const> calldata) noexcept
        {
            result_ = evmc::Result();
            output_data_ = {};

            host_.accounts[msg_.sender].balance =
                std::numeric_limits<uint256_t>::max()
                    .template store_be<evmc::bytes32>();

            msg_.gas = gas_limit;
            msg_.input_data = calldata.data();
            msg_.input_size = calldata.size();

            if (TraitsTest<T>::Trait::evm_rev() >= EVMC_BERLIN) {
                host_.access_account(msg_.sender);
                host_.access_account(msg_.recipient);
            }
        }

        void execute(
            std::int64_t gas_limit, std::span<std::uint8_t const> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept
        {
            pre_execute(gas_limit, calldata);

            auto icode = make_shared_intercode(code);

            if (impl == Compiler) {
                auto ncode =
                    vm_.compiler().compile<typename TraitsTest<T>::Trait>(
                        icode);

                ASSERT_TRUE(ncode->entrypoint() != nullptr);
                result_ = evmc::Result{vm_.execute_native_entrypoint_raw(
                    &host_.get_interface(),
                    host_.to_context(),
                    &msg_,
                    icode,
                    ncode->entrypoint())};
            }
            else if (impl == Interpreter) {
                result_ =
                    vm_.execute_intercode_raw<typename TraitsTest<T>::Trait>(
                        &host_.get_interface(),
                        host_.to_context(),
                        &msg_,
                        icode);
            }
            else {
                MONAD_VM_ASSERT(impl == Evmone);
                evmc::VM const evmone_vm{evmc_create_evmone()};

                result_ = evmc::Result{::evmone::baseline::execute(
                    *static_cast<::evmone::VM *>(evmone_vm.get_raw_pointer()),
                    host_.get_interface(),
                    host_.to_context(),
                    TraitsTest<T>::Trait::evm_rev(),
                    msg_,
                    evmone::baseline::analyze(evmc::bytes_view(code)))};
            }
        }

        void execute(
            std::int64_t gas_limit, std::initializer_list<std::uint8_t> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept
        {
            execute(gas_limit, std::span{code}, calldata, impl);
        }

        void execute(
            std::span<std::uint8_t const> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept
        {
            execute(
                std::numeric_limits<std::int64_t>::max(), code, calldata, impl);
        }

        void execute(
            std::initializer_list<std::uint8_t> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept
        {
            execute(std::span{code}, calldata, impl);
        }

        bool has_empty_state() const noexcept
        {
            return host_.accounts.empty() &&
                   host_.recorded_account_accesses.empty() &&
                   host_.recorded_blockhashes.empty() &&
                   host_.recorded_calls.empty() &&
                   host_.recorded_logs.empty() &&
                   host_.recorded_selfdestructs.empty();
        }

    public:
        void execute_and_compare(
            std::int64_t gas_limit, std::span<std::uint8_t const> code,
            std::span<std::uint8_t const> calldata = {}) noexcept
        {
            // This comparison shouldn't be called multiple times in one test;
            // if any state has been recorded on this host before we begin a
            // test, the test should fail and stop us from trying to make
            // assertions about a broken state.
            ASSERT_TRUE(has_empty_state());

            execute(gas_limit, code, calldata, Compiler);
            auto actual = std::move(result_);

            // We need to reset the host between executions; otherwise the state
            // maintained will produce inconsistent results (e.g. an account is
            // touched by the first run, then is subsequently warm for the
            // second one).
            host_ = {};

            execute(gas_limit, code, calldata, Evmone);
            auto expected = std::move(result_);

            switch (expected.status_code) {
            case EVMC_SUCCESS:
            case EVMC_REVERT:
                ASSERT_EQ(actual.status_code, expected.status_code);
                break;
            default:
                ASSERT_NE(actual.status_code, EVMC_SUCCESS);
                ASSERT_NE(actual.status_code, EVMC_REVERT);
                break;
            }

            ASSERT_EQ(actual.gas_left, expected.gas_left);
            ASSERT_EQ(actual.gas_refund, expected.gas_refund);
            ASSERT_EQ(actual.output_size, expected.output_size);

            ASSERT_TRUE(std::equal(
                actual.output_data,
                actual.output_data + actual.output_size,
                expected.output_data));

            ASSERT_EQ(
                evmc::address(actual.create_address),
                evmc::address(expected.create_address));
        }

        void execute_and_compare(
            std::int64_t gas_limit, std::initializer_list<std::uint8_t> code,
            std::span<std::uint8_t const> calldata = {}) noexcept
        {
            execute_and_compare(gas_limit, std::span{code}, calldata);
        }
    };

    template <typename T>
    class VMTraitsTest
        : public VMTraitsTestBase<T>
        , public ::testing::Test
    {

    protected:
        VMTraitsTest() noexcept = default;
    };

    class VMFileTest
        : public testing::Test
        , public testing::WithParamInterface<std::tuple<
              fs::directory_entry, std::variant<evmc_revision, monad_revision>>>
    {
    protected:
        template <Traits traits>
        static void execute_and_compare_evm_rev(
            std::int64_t gas_limit, std::span<std::uint8_t const> code) noexcept
        {
            VMTraitsTestBase<::detail::EvmRevisionConstant<traits::evm_rev()>>
                test;
            test.execute_and_compare(gas_limit, code);
        }

        template <Traits traits>
        static void execute_and_compare_monad_rev(
            std::int64_t gas_limit, std::span<std::uint8_t const> code) noexcept
        {
            VMTraitsTestBase<
                ::detail::MonadRevisionConstant<traits::monad_rev()>>
                test;
            test.execute_and_compare(gas_limit, code);
        }

        void execute_and_compare(
            std::int64_t gas_limit, std::span<std::uint8_t const> code,
            std::variant<evmc_revision, monad_revision> rev_) noexcept
        {
            if (std::holds_alternative<evmc_revision>(rev_)) {
                auto rev = std::get<evmc_revision>(rev_);
                SWITCH_EVM_TRAITS(
                    VMFileTest::execute_and_compare_evm_rev, gas_limit, code);
            }
            else {
                auto rev = std::get<monad_revision>(rev_);
                SWITCH_MONAD_TRAITS(
                    VMFileTest::execute_and_compare_monad_rev, gas_limit, code);
            }
        }
    };
}

TYPED_TEST_SUITE(
    VMTraitsTest, ::detail::MonadEvmRevisionTypes,
    ::detail::RevisionTestNameGenerator);
