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
};

struct ReserveBalanceEvm : public ReserveBalance
{
    static constexpr auto update_selector =
        abi_encode_selector("update(uint256)");

    BlockHashBufferFinalized const block_hash_buffer;
    MonadDevnet chain;

    EvmcHost<MonadTraits<MONAD_NEXT>> h{
        call_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
    };
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
