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
#include <category/execution/ethereum/trace/tracer_config.h>
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
        std::filesystem::path dbname;
        OnDiskMachine machine;
        mpt::Db db;
        TrieDb tdb;
        vm::VM vm;
        BlockState block_state;
        monad::fiber::PriorityPool pool{2, 4}; // 2 threads, 4 fibers

        StateAtFixture()
            : dbname{[] {
                std::filesystem::path dbname(
                    MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                    "monad_eth_call_test1_XXXXXX");
                int const fd = ::mkstemp((char *)dbname.native().data());
                MONAD_ASSERT(fd != -1);
                MONAD_ASSERT(
                    -1 !=
                    ::ftruncate(
                        fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
                ::close(fd);
                return dbname;
            }()}
            , db{machine,
                 mpt::OnDiskDbConfig{.append = false, .dbname_paths = {dbname}}}
            , tdb{db}
            , block_state{tdb, vm}
        {
        }

        ~StateAtFixture()
        {
            std::filesystem::remove(dbname);
        }

        Transaction make_tx(std::optional<Address> to = std::nullopt);
        void deploy_counter_contract(uint64_t block_number);
    };

    Transaction StateAtFixture::make_tx(std::optional<Address> to)
    {
        MonadDevnet devnet;
        Transaction tx;
        tx.gas_limit = 100'000'000;
        tx.nonce = next_tx_nonce++;
        tx.to = to;
        tx.sc = SignatureAndChain{1, 1, devnet.get_chain_id(), 1};
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

    std::vector<Address> senders(size_t n)
    {
        std::vector<Address> s(n, addr1);
        return s;
    }

    std::pair<
        std::vector<nlohmann::json>,
        std::vector<std::unique_ptr<trace::StateTracer>>>
    make_state_tracers(size_t n, enum monad_tracer_config config)
    {
        std::vector<nlohmann::json> trace_containers{};
        trace_containers.reserve(n);
        std::vector<std::unique_ptr<trace::StateTracer>> state_tracers{};
        state_tracers.reserve(n);
        for (size_t i = 0; i < n; ++i) {
            trace_containers.push_back(nlohmann::json{});
            state_tracers.push_back([&] -> std::unique_ptr<trace::StateTracer> {
                switch (config) {
                case NOOP_TRACER:
                    return std::unique_ptr<trace::StateTracer>{
                        std::make_unique<trace::StateTracer>(std::monostate{})};
                case CALL_TRACER:
                    MONAD_ASSERT(false);
                    break;
                case PRESTATE_TRACER:
                    return std::unique_ptr<trace::StateTracer>{
                        std::make_unique<trace::StateTracer>(
                            trace::PrestateTracer{trace_containers[i]})};
                case STATEDIFF_TRACER:
                    return std::unique_ptr<trace::StateTracer>{
                        std::make_unique<trace::StateTracer>(
                            trace::StateDiffTracer{trace_containers[i]})};
                }
                MONAD_ASSERT(false);
            }());
        }
        MONAD_ASSERT(state_tracers.size() == n);
        MONAD_ASSERT(trace_containers.size() == state_tracers.size());
        return std::pair<
            std::vector<nlohmann::json>,
            std::vector<std::unique_ptr<trace::StateTracer>>>{
            std::move(trace_containers), std::move(state_tracers)};
    }
}

TEST_F(StateAtFixture, check_nonce)
{
    State state{block_state, Incarnation{0, 0}};
    state.create_contract(addr1);
    state.add_to_balance(addr1, 1'000'000);
    state.create_contract(addr2);
    state.add_to_balance(addr2, 1'000'000);
    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(std::move(state));

    BlockHeader header{.number = 1};
    std::vector<Transaction> txns{make_tx(addr1), make_tx(addr1)};
    auto [trace_containers, state_tracers] =
        make_state_tracers(txns.size(), NOOP_TRACER);

    EXPECT_EQ(block_state.read_account(addr1).value().nonce, 0);
    auto const result = state_after_transactions<traits>(
        chain,
        header,
        txns,
        ::senders(txns.size()),
        ::authorities(txns.size()),
        block_state,
        buffer,
        pool,
        state_tracers);
    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value().size(), txns.size());
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
    std::vector<Transaction> txns{make_tx(counter_addr), make_tx(counter_addr)};
    auto [trace_containers, state_tracers] =
        make_state_tracers(txns.size(), STATEDIFF_TRACER);

    bytes32_t const value_slot{};
    EXPECT_EQ(
        block_state.read_storage(counter_addr, Incarnation{1, 0}, value_slot),
        bytes32_t{});
    auto const result = state_after_transactions<traits>(
        chain,
        header,
        txns,
        ::senders(txns.size()),
        ::authorities(txns.size()),
        block_state,
        buffer,
        pool,
        state_tracers);

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value().size(), txns.size());

    bytes32_t const expected_value = to_bytes(to_big_endian(uint256_t{2}));
    EXPECT_EQ(
        block_state.read_storage(counter_addr, Incarnation{1, 0}, value_slot),
        expected_value);

    std::string const expected_trace1 = R"({
  "post": {
    "0x6363636363636363636363636363636363636363": {
      "storage": {
        "0x0000000000000000000000000000000000000000000000000000000000000000": "0x0000000000000000000000000000000000000000000000000000000000000001"
      }
    },
    "0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56": {
      "nonce": 1
    }
  },
  "pre": {
    "0x6363636363636363636363636363636363636363": {
      "balance": "0x0",
      "code": "0x60015f54015f55"
    },
    "0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56": {
      "balance": "0xf4240"
    }
  }
})";
    EXPECT_EQ(trace_containers[0].dump(2), expected_trace1);

    std::string const expected_trace2 = R"({
  "post": {
    "0x6363636363636363636363636363636363636363": {
      "storage": {
        "0x0000000000000000000000000000000000000000000000000000000000000000": "0x0000000000000000000000000000000000000000000000000000000000000002"
      }
    },
    "0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56": {
      "nonce": 2
    }
  },
  "pre": {
    "0x6363636363636363636363636363636363636363": {
      "balance": "0x0",
      "code": "0x60015f54015f55",
      "storage": {
        "0x0000000000000000000000000000000000000000000000000000000000000000": "0x0000000000000000000000000000000000000000000000000000000000000001"
      }
    },
    "0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56": {
      "balance": "0xf4240",
      "nonce": 1
    }
  }
})";
    EXPECT_EQ(trace_containers[1].dump(2), expected_trace2);
}
