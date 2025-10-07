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

#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_at.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/vm.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;
using namespace monad::test;
using namespace monad::trace;

namespace
{

    using traits = MonadTraits<MONAD_FIVE>;

    static constexpr auto addr1{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto addr2{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto counter_addr{
        0x6363636363636363636363636363636363636363_address};

    struct StateAtFixture : public ::testing::Test
    {
        MonadDevnet chain;
        BlockHashBufferFinalized buffer;
        uint64_t next_tx_nonce = 0;
        InMemoryMachine machine;
        mpt::Db db;
        TrieDb tdb;
        vm::VM vm;
        BlockState block_state;

        StateAtFixture()
            : db{machine}
            , tdb{db}
            , block_state{tdb, vm}
        {
        }

        Transaction make_tx(std::optional<Address> to = std::nullopt);
        void deploy_counter_contract(uint64_t block_number);
    };

    Transaction StateAtFixture::make_tx(std::optional<Address> to)
    {
        Transaction tx;
        tx.gas_limit = 100'000;
        tx.nonce = next_tx_nonce++;
        tx.to = to;
        return tx;
    }

    void StateAtFixture::deploy_counter_contract(uint64_t block_number)
    {
        using namespace monad::vm::utils;
        auto eb = evm_as::latest();

        eb.push(1).push0().sload().add().push0().sstore();

        std::vector<uint8_t> bytecode{};
        evm_as::compile(eb, bytecode);

        byte_string code{bytecode.data(), bytecode.data() + bytecode.size()};

        State state{block_state, Incarnation{block_number, 0}};
        state.create_contract(counter_addr);
        state.set_code(counter_addr, code);
        state.set_code_hash(counter_addr, to_bytes(keccak256(code)));

        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
    }

    std::vector<std::vector<std::optional<Address>>> authorities(size_t n)
    {
        std::vector<std::vector<std::optional<Address>>> auths(
            n, std::vector<std::optional<Address>>(0));
        return auths;
    }

    std::vector<std::optional<Address>> senders(size_t n)
    {
        std::vector<std::optional<Address>> s(n, addr1);
        return s;
    }
}

TEST_F(StateAtFixture, simple)
{
    State state{block_state, Incarnation{0, 0}};
    state.create_contract(addr1);
    state.add_to_balance(addr1, 1'000'000);
    state.create_contract(addr2);
    state.add_to_balance(addr2, 1'000'000);
    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(std::move(state));

    BlockHeader header{.number = 1};
    NoopCallTracer call_tracer{};
    trace::StateTracer state_tracer = std::monostate{};
    std::vector<Transaction> txns{make_tx(addr1), make_tx(addr1)};

    EXPECT_EQ(block_state.read_account(addr1).value().nonce, 0);
    state_after_transactions<traits>(
        chain,
        header,
        buffer,
        call_tracer,
        state_tracer,
        block_state,
        ::senders(txns.size()),
        ::authorities(txns.size()),
        txns);
    EXPECT_EQ(block_state.read_account(addr1).value().nonce, 2);
}

TEST_F(StateAtFixture, counter_contract)
{
    State state{block_state, Incarnation{0, 0}};
    state.create_contract(addr1);
    state.add_to_balance(addr1, 1'000'000);
    state.create_contract(addr2);
    state.add_to_balance(addr2, 1'000'000);
    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(std::move(state));

    deploy_counter_contract(1);
    BlockHeader header{.number = 2};
    NoopCallTracer call_tracer{};
    trace::StateTracer state_tracer = std::monostate{};
    std::vector<Transaction> txns{make_tx(counter_addr), make_tx(counter_addr)};

    bytes32_t const value_slot{};
    EXPECT_EQ(
        block_state.read_storage(
            counter_addr, Incarnation{1, Incarnation::LAST_TX}, value_slot),
        bytes32_t{});
    state_after_transactions<traits>(
        chain,
        header,
        buffer,
        call_tracer,
        state_tracer,
        block_state,
        ::senders(txns.size()),
        ::authorities(txns.size()),
        txns);

    bytes32_t const expected_value = to_bytes(to_big_endian(uint256_t{2}));
    EXPECT_EQ(
        block_state.read_storage(
            counter_addr, Incarnation{2, Incarnation::LAST_TX}, value_slot),
        expected_value);
}
