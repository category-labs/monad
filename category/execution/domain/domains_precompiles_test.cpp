// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

using namespace monad;

namespace
{
    using traits = MonadTraits<MONAD_TEN>;

    struct DomainPrecompilesTest : ::testing::Test
    {
        vm::VM vm;
        mpt::Db db{std::make_unique<MonadInMemoryMachine>()};
        TrieDb trie_db{db};
        BlockState block_state{trie_db, vm};
        State state{block_state, Incarnation{0, 0}};
        NoopCallTracer call_tracer;
    };
}

TEST_F(DomainPrecompilesTest, classification_excludes_monad_precompiles)
{
    EXPECT_TRUE(is_precompile<traits>(Address{1}));
    EXPECT_TRUE(is_precompile<traits>(Address{4}));
    EXPECT_FALSE(is_precompile<traits>(staking::STAKING_CA));
    EXPECT_FALSE(is_precompile<traits>(RESERVE_BALANCE_CA));
    EXPECT_FALSE(is_precompile<traits>(Address{0x1234}));
}

TEST_F(DomainPrecompilesTest, dispatch_uses_ethereum_precompiles)
{
    byte_string const input{0x01, 0x02, 0x03};
    vm::Message const identity{
        .kind = vm::CallKind::Call,
        .gas = 1'000,
        .recipient = Address{4},
        .input_data = input.data(),
        .input_size = input.size(),
        .code_address = Address{4}};
    auto const result =
        check_call_precompile<traits>(state, call_tracer, identity, false);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->status_code, CallStatus::Success);
    EXPECT_EQ(result->gas_left, 982);
    EXPECT_EQ(
        (byte_string_view{result->output_data, result->output_size}), input);

    for (auto const &address :
         {staking::STAKING_CA, RESERVE_BALANCE_CA, Address{0x1234}}) {
        vm::Message const msg{.code_address = address};
        EXPECT_FALSE(
            check_call_precompile<traits>(state, call_tracer, msg, false)
                .has_value());
    }
}

TEST_F(DomainPrecompilesTest, host_warms_only_ethereum_precompiles)
{
    auto chain_ctx = ChainContext<traits>::debug_empty();
    chain_ctx.private_domain = true;
    BlockHashBufferFinalized const block_hashes;
    Transaction const tx{};
    trace::StateTracer state_tracer{std::monostate{}};
    StateHost<traits> host{
        call_tracer,
        state_tracer,
        EMPTY_TX_CONTEXT,
        block_hashes,
        state,
        tx,
        std::nullopt,
        0,
        chain_ctx};
    EXPECT_EQ(host.access_account(Address{1}), AccessStatus::Warm);
    EXPECT_EQ(host.access_account(Address{4}), AccessStatus::Warm);
    for (auto const &address :
         {staking::STAKING_CA, RESERVE_BALANCE_CA, Address{0x1234}}) {
        EXPECT_EQ(host.access_account(address), AccessStatus::Cold);
        EXPECT_EQ(host.access_account(address), AccessStatus::Warm);
    }
}

TEST_F(DomainPrecompilesTest, access_list_includes_disabled_monad_precompiles)
{
    for (auto const &address :
         {Address{1}, Address{4}, staking::STAKING_CA, RESERVE_BALANCE_CA}) {
        (void)state.access_account(address);
    }
    nlohmann::json output;
    std::vector<std::optional<Address>> const authorities;
    trace::AccessListTracer tracer{
        output, Address{}, Address{}, std::nullopt, authorities};
    tracer.encode<traits>(state);
    std::vector<Address> addresses;
    for (auto const &entry : output) {
        addresses.push_back(
            *from_hex<Address>(entry["address"].get<std::string>()));
    }
    EXPECT_EQ(
        addresses,
        (std::vector<Address>{staking::STAKING_CA, RESERVE_BALANCE_CA}));
}
