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

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;

struct ReserveBalance : public ::testing::Test
{
    static constexpr auto account_a = Address{0xdeadbeef};
    static constexpr auto account_b = Address{0xcafebabe};

    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    ReserveBalanceContract contract{state};
};

TEST_F(ReserveBalance, get_default)
{
    EXPECT_EQ(contract.get(account_a), DEFAULT_RESERVE_BALANCE_WEI);
}

TEST_F(ReserveBalance, set_then_get)
{
    EXPECT_EQ(contract.get(account_a).native(), DEFAULT_RESERVE_BALANCE_WEI);
    EXPECT_EQ(contract.get(account_b).native(), DEFAULT_RESERVE_BALANCE_WEI);

    contract.set(account_a, uint256_t{123});
    EXPECT_EQ(contract.get(account_a).native(), 123);
    EXPECT_EQ(contract.get(account_b).native(), DEFAULT_RESERVE_BALANCE_WEI);

    contract.set(account_a, uint256_t{0});
    EXPECT_EQ(contract.get(account_a).native(), DEFAULT_RESERVE_BALANCE_WEI);
    EXPECT_EQ(contract.get(account_b).native(), DEFAULT_RESERVE_BALANCE_WEI);
}

struct ReserveBalanceEvm : public ReserveBalance
{
    static constexpr auto get_selector = abi_encode_selector("get()");
    static constexpr auto set_selector = abi_encode_selector("set(uint256)");

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    MonadDevnet chain;

    EvmcHost<MonadTraits<MONAD_FOUR>> h{
        chain,
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        MAX_CODE_SIZE_MONAD_TWO,
        MAX_INITCODE_SIZE_MONAD_FOUR,
    };
};

TEST_F(ReserveBalanceEvm, precompile_get)
{
    auto input = std::array<uint8_t, 4>{};
    intx::be::unsafe::store(input.data(), get_selector);

    auto const m = evmc_message{
        .gas = 8100,
        .recipient = RESERVE_BALANCE_CA,
        .sender = account_a,
        .input_data = input.data(),
        .input_size = input.size(),
        .code_address = RESERVE_BALANCE_CA,
    };

    auto const result = h.call(m);
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.gas_refund, 0);
    EXPECT_EQ(result.output_size, 32);
    EXPECT_EQ(
        intx::be::unsafe::load<uint256_t>(result.output_data),
        DEFAULT_RESERVE_BALANCE_WEI);
}

TEST_F(ReserveBalanceEvm, precompile_set_then_get)
{
    {
        auto set_input = std::array<uint8_t, 36>{};
        intx::be::unsafe::store(set_input.data(), set_selector);

        auto const set_value = u256_be{123};
        auto const encoded_arg = abi_encode_uint(set_value);
        std::ranges::copy(encoded_arg.bytes, set_input.data() + 4);

        auto const set_m = evmc_message{
            .gas = 15275,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = set_input.data(),
            .input_size = set_input.size(),
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const set_result = h.call(set_m);
        EXPECT_EQ(set_result.status_code, EVMC_SUCCESS);
        EXPECT_EQ(set_result.gas_left, 0);
        EXPECT_EQ(set_result.gas_refund, 0);
        EXPECT_EQ(set_result.output_size, 32);
        EXPECT_EQ(intx::be::unsafe::load<uint256_t>(set_result.output_data), 1);
    }

    {
        auto get_input = std::array<uint8_t, 4>{};
        intx::be::unsafe::store(get_input.data(), get_selector);

        auto const get_m = evmc_message{
            .gas = 8100,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = get_input.data(),
            .input_size = get_input.size(),
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const get_result = h.call(get_m);
        EXPECT_EQ(get_result.status_code, EVMC_SUCCESS);
        EXPECT_EQ(get_result.gas_left, 0);
        EXPECT_EQ(get_result.gas_refund, 0);
        EXPECT_EQ(get_result.output_size, 32);
        EXPECT_EQ(
            intx::be::unsafe::load<uint256_t>(get_result.output_data), 123);
    }

    {
        auto reset_input = std::array<uint8_t, 36>{};
        intx::be::unsafe::store(reset_input.data(), set_selector);

        auto const reset_m = evmc_message{
            .gas = 15275,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = reset_input.data(),
            .input_size = reset_input.size(),
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const reset_result = h.call(reset_m);
        EXPECT_EQ(reset_result.status_code, EVMC_SUCCESS);
        EXPECT_EQ(reset_result.gas_left, 0);
        EXPECT_EQ(reset_result.gas_refund, 0);
        EXPECT_EQ(reset_result.output_size, 32);
        EXPECT_EQ(
            intx::be::unsafe::load<uint256_t>(reset_result.output_data), 1);
    }

    {
        auto get_input = std::array<uint8_t, 4>{};
        intx::be::unsafe::store(get_input.data(), get_selector);

        auto const get_m = evmc_message{
            .gas = 8100,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = get_input.data(),
            .input_size = get_input.size(),
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const get_result = h.call(get_m);
        EXPECT_EQ(get_result.status_code, EVMC_SUCCESS);
        EXPECT_EQ(get_result.gas_left, 0);
        EXPECT_EQ(get_result.gas_refund, 0);
        EXPECT_EQ(get_result.output_size, 32);
        EXPECT_EQ(
            intx::be::unsafe::load<uint256_t>(get_result.output_data),
            DEFAULT_RESERVE_BALANCE_WEI);
    }
}

TEST_F(ReserveBalanceEvm, precompile_fallback)
{
    auto input = std::array<uint8_t, 4>{};

    auto const m = evmc_message{
        .gas = 40'000,
        .recipient = RESERVE_BALANCE_CA,
        .sender = account_a,
        .input_data = input.data(),
        .input_size = input.size(),
        .code_address = RESERVE_BALANCE_CA,
    };

    auto const result = h.call(m);
    EXPECT_EQ(result.status_code, EVMC_REVERT);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.gas_refund, 0);
    EXPECT_EQ(result.output_size, 20);

    auto const message = std::string_view{
        reinterpret_cast<char const *>(result.output_data), 20};
    EXPECT_EQ(message, "method not supported");
}
