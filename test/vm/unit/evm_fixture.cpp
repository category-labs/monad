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

#include "evm_fixture.hpp"

#include <category/vm/code.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>

#include <evmc/bytes.hpp>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <evmone/baseline.hpp>
#include <evmone/evmone.h>
#include <evmone/vm.hpp>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <limits>
#include <span>
#include <utility>

namespace monad::vm::compiler::test
{
    void EvmTest::pre_execute(
        std::int64_t gas_limit, std::span<std::uint8_t const> calldata) noexcept
    {
        result_ = evmc::Result();
        output_data_ = {};

        host_.accounts[msg_.sender].balance =
            std::numeric_limits<uint256_t>::max()
                .template store_be<evmc::bytes32>();

        msg_.gas = gas_limit;
        msg_.input_data = calldata.data();
        msg_.input_size = calldata.size();

        if (rev_ >= EVMC_BERLIN) {
            host_.access_account(msg_.sender);
            host_.access_account(msg_.recipient);
        }
    }

    void EvmTest::execute(
        std::int64_t gas_limit, std::span<std::uint8_t const> code,
        std::span<std::uint8_t const> calldata, Implementation impl) noexcept
    {
        pre_execute(gas_limit, calldata);

        auto icode = make_shared_intercode(code);

        if (impl == Compiler) {
            auto ncode = vm_.compiler().compile(rev_, icode);
            ASSERT_TRUE(ncode->entrypoint() != nullptr);
            result_ = evmc::Result{vm_.execute_native_entrypoint(
                &host_.get_interface(),
                host_.to_context(),
                &msg_,
                icode,
                ncode->entrypoint())};
        }
        else if (impl == Interpreter) {
            result_ = evmc::Result{vm_.execute_intercode(
                rev_,
                &host_.get_interface(),
                host_.to_context(),
                &msg_,
                icode)};
        }
        else {
            MONAD_VM_ASSERT(impl == Evmone);
            evmc::VM const evmone_vm{evmc_create_evmone()};

            result_ = evmc::Result{::evmone::baseline::execute(
                *static_cast<::evmone::VM *>(evmone_vm.get_raw_pointer()),
                host_.get_interface(),
                host_.to_context(),
                rev_,
                msg_,
                evmone::baseline::analyze(evmc::bytes_view(code), false))};
        }
    }

    void EvmTest::execute(
        std::int64_t gas_limit, std::initializer_list<std::uint8_t> code,
        std::span<std::uint8_t const> calldata, Implementation impl) noexcept
    {
        execute(gas_limit, std::span{code}, calldata, impl);
    }

    void EvmTest::execute(
        std::span<std::uint8_t const> code,
        std::span<std::uint8_t const> calldata, Implementation impl) noexcept
    {
        execute(std::numeric_limits<std::int64_t>::max(), code, calldata, impl);
    }

    void EvmTest::execute(
        std::initializer_list<std::uint8_t> code,
        std::span<std::uint8_t const> calldata, Implementation impl) noexcept
    {
        execute(std::span{code}, calldata, impl);
    }

    void EvmTest::execute_and_compare(
        std::int64_t gas_limit, std::span<std::uint8_t const> code,
        std::span<std::uint8_t const> calldata) noexcept
    {
        // This comparison shouldn't be called multiple times in one test; if
        // any state has been recorded on this host before we begin a test, the
        // test should fail and stop us from trying to make assertions about a
        // broken state.
        ASSERT_TRUE(has_empty_state());

        execute(gas_limit, code, calldata, Compiler);
        auto actual = std::move(result_);

        // We need to reset the host between executions; otherwise the state
        // maintained will produce inconsistent results (e.g. an account is
        // touched by the first run, then is subsequently warm for the second
        // one).
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

    void EvmTest::execute_and_compare(
        std::int64_t gas_limit, std::initializer_list<std::uint8_t> code,
        std::span<std::uint8_t const> calldata) noexcept
    {
        execute_and_compare(gas_limit, std::span{code}, calldata);
    }

    bool EvmTest::has_empty_state() const noexcept
    {
        return host_.accounts.empty() &&
               host_.recorded_account_accesses.empty() &&
               host_.recorded_blockhashes.empty() &&
               host_.recorded_calls.empty() && host_.recorded_logs.empty() &&
               host_.recorded_selfdestructs.empty();
    }
}
