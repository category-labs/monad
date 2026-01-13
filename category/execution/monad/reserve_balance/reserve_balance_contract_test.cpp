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
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>
#include <boost/outcome/result.hpp>
#include <evmc/evmc.h>
#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <limits>

using namespace monad;

struct ReserveBalance : public ::testing::Test
{
    static constexpr auto account_a = Address{0xdeadbeef};
    static constexpr auto account_b = Address{0xcafebabe};
    static constexpr auto account_c = Address{0xabbaabba};

    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    NoopCallTracer call_tracer;
    ReserveBalanceContract contract{state, call_tracer};
    ReserveBalanceView reserve_view{state};
};

TEST_F(ReserveBalance, get_get)
{
    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_a), DEFAULT_RESERVE_BALANCE_WEI);
    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_a), DEFAULT_RESERVE_BALANCE_WEI);

    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_b), DEFAULT_RESERVE_BALANCE_WEI);
    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_b), DEFAULT_RESERVE_BALANCE_WEI);
}

TEST_F(ReserveBalance, update_get)
{
    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_a), DEFAULT_RESERVE_BALANCE_WEI);
    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_b), DEFAULT_RESERVE_BALANCE_WEI);

    Result<uint256_t> old_value =
        contract.update(state, account_a, uint256_t{123});
    ASSERT_TRUE(old_value);
    EXPECT_EQ(old_value.value(), DEFAULT_RESERVE_BALANCE_WEI);
    EXPECT_EQ(reserve_view.get_delayed_urb(account_a), 123);
    EXPECT_EQ(
        reserve_view.get_delayed_urb(account_b), DEFAULT_RESERVE_BALANCE_WEI);

    Result<uint256_t> old_value_2 = contract.update(state, account_a, 0);
    ASSERT_FALSE(old_value_2);
    // ASSERT_TRUE(old_value_2);
    // EXPECT_EQ(old_value_2.value(), uint256_t{123});
    // EXPECT_EQ(
    //     reserve_view.get_delayed_urb(account_a),
    //     DEFAULT_RESERVE_BALANCE_WEI);
    // EXPECT_EQ(
    //     reserve_view.get_delayed_urb(account_b),
    //     DEFAULT_RESERVE_BALANCE_WEI);
}

struct ReserveBalanceEvm : public ReserveBalance
{
    static constexpr auto update_selector =
        abi_encode_selector("update(uint256)");

    BlockHashBufferFinalized const block_hash_buffer;
    Transaction const empty_tx{};

    ankerl::unordered_dense::segmented_set<Address> const
        grandparent_senders_and_authorities{};
    ankerl::unordered_dense::segmented_set<Address> const
        parent_senders_and_authorities{};
    ankerl::unordered_dense::segmented_set<Address> const
        senders_and_authorities{};
    // The {}s are needed here to pass the 0 < senders.size() assertion checks
    // in `dipped_into_reserve`.
    std::vector<Address> const senders{{}};
    std::vector<std::vector<std::optional<Address>>> const authorities{{}};
    ChainContext<MonadTraits<MONAD_NEXT>> const chain_ctx{
        grandparent_senders_and_authorities,
        parent_senders_and_authorities,
        senders_and_authorities,
        senders,
        authorities};

    EvmcHost<MonadTraits<MONAD_NEXT>> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        empty_tx,
        0,
        0,
        chain_ctx};
};

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

TEST_F(ReserveBalanceEvm, precompile_update_get)
{
    {
        auto update_input = std::array<uint8_t, 36>{};
        intx::be::unsafe::store(update_input.data(), update_selector);
        auto const update_value = u256_be{123};
        auto const encoded_arg = abi_encode_uint(update_value);
        std::ranges::copy(encoded_arg.bytes, update_input.data() + 4);

        auto const update_m = evmc_message{
            .gas = 15275,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = update_input.data(),
            .input_size = update_input.size(),
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const update_result = h.call(update_m);
        EXPECT_EQ(update_result.status_code, EVMC_SUCCESS);
        EXPECT_EQ(update_result.gas_left, 0);
        EXPECT_EQ(update_result.gas_refund, 0);
        EXPECT_EQ(update_result.output_size, 32);
        EXPECT_EQ(
            intx::be::unsafe::load<uint256_t>(update_result.output_data), 1);

        EXPECT_EQ(reserve_view.get_delayed_urb(account_a), 123);
    }

    {
        auto reset_input = std::array<uint8_t, 36>{};
        intx::be::unsafe::store(reset_input.data(), update_selector);

        auto const reset_m = evmc_message{
            .gas = 15275,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = reset_input.data(),
            .input_size = reset_input.size(),
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const reset_result = h.call(reset_m);
        EXPECT_EQ(reset_result.status_code, EVMC_REVERT);
        EXPECT_EQ(reset_result.gas_left, 0);
        EXPECT_EQ(reset_result.gas_refund, 0);
        EXPECT_EQ(reset_result.output_size, 14);
        auto const message = std::string_view{
            reinterpret_cast<char const *>(reset_result.output_data), 14};
        EXPECT_EQ(message, "pending update");
    }
}

TEST_F(ReserveBalanceEvm, precompile_non_payable_function)
{
    {
        state.add_to_balance(account_c, std::numeric_limits<uint256_t>::max());
        auto input = std::array<uint8_t, 36>{};
        intx::be::unsafe::store(input.data(), update_selector);
        auto const update_value = u256_be{123};
        auto const encoded_arg = abi_encode_uint(update_value);
        std::ranges::copy(encoded_arg.bytes, input.data() + 4);

        bytes32_t value;
        {
            static_assert(sizeof(evmc_uint256be) == sizeof(uint256_t));
            uint256_t temp{12345};
            std::memcpy(value.bytes, &temp, sizeof(uint256_t));
        }

        auto const m = evmc_message{
            .gas = 15275,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_c,
            .input_data = input.data(),
            .input_size = input.size(),
            .value = evmc_uint256be{.bytes = {1}},
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const result = h.call(m);
        EXPECT_EQ(result.status_code, EVMC_REVERT);
        EXPECT_EQ(result.gas_left, 0);
        EXPECT_EQ(result.gas_refund, 0);
        EXPECT_EQ(result.output_size, 14);

        auto const message = std::string_view{
            reinterpret_cast<char const *>(result.output_data), 14};
        EXPECT_EQ(message, "value non-zero");
    }

    {
        auto input = std::array<uint8_t, 36>{};
        intx::be::unsafe::store(input.data(), update_selector);
        auto const update_value = u256_be{123};
        auto const encoded_arg = abi_encode_uint(update_value);
        std::ranges::copy(encoded_arg.bytes, input.data() + 4);

        auto const m = evmc_message{
            .gas = 15275,
            .recipient = RESERVE_BALANCE_CA,
            .sender = account_a,
            .input_data = input.data(),
            .input_size = input.size(),
            .value = evmc_uint256be{.bytes = {1}},
            .code_address = RESERVE_BALANCE_CA,
        };

        auto const result = h.call(m);
        EXPECT_EQ(result.status_code, EVMC_INSUFFICIENT_BALANCE);
        EXPECT_EQ(result.gas_left, 15275);
        EXPECT_EQ(result.gas_refund, 0);
        EXPECT_EQ(result.output_size, 0);
    }
}

TEST_F(ReserveBalance, is_reconfigurable_transaction)
{
    auto const calldata = [](uint32_t const selector,
                             uint256_t value) -> byte_string {
        std::array<uint8_t, 36> input{};
        intx::be::unsafe::store(input.data(), selector);
        auto const encoded_arg = abi_encode_uint(u256_be{value});
        std::ranges::copy(encoded_arg.bytes, input.data() + 4);
        return byte_string{input.data(), input.data() + input.size()};
    };

    {
        Transaction const tx{
            .to = RESERVE_BALANCE_CA,
            .data = calldata(abi_encode_selector("update(uint256)"), 123)};

        EXPECT_TRUE(is_reconfiguring_transaction(tx));
    }

    {
        Transaction const tx{
            .to = RESERVE_BALANCE_CA,
            .data = calldata(abi_encode_selector("update(uint256)"), 0)};

        EXPECT_TRUE(is_reconfiguring_transaction(tx));
    }

    {
        Transaction const tx{
            .to = RESERVE_BALANCE_CA,
            .data = calldata(abi_encode_selector("updaté(uint256)"), 0)};

        EXPECT_FALSE(is_reconfiguring_transaction(tx));
    }

    {
        Transaction const tx{
            .value = 1,
            .to = RESERVE_BALANCE_CA,
            .data = calldata(abi_encode_selector("update(uint256)"), 123)};

        EXPECT_FALSE(is_reconfiguring_transaction(tx));
    }
}
