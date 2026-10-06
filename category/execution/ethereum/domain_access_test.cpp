// Copyright (C) 2026 Category Labs, Inc.
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

// The access check the domain arm runs before every EVM call.
//
// It is tested here and not through the corpus, which cannot reach it: the
// corpus deploys the spoke this tree vendors, from before the rename, and that
// contract has no canCall at all -- so against it every call is denied, which
// is correct behaviour against a stale fixture and tells you nothing about the
// rule. CONFORMANCE.md carries that.
//
// So the spoke here is a handful of bytes that answers the one way or the
// other, which is all the rule reads.

#ifdef MONAD_ZKVM_L2

    #include <category/core/address.hpp>
    #include <category/core/byte_string.hpp>
    #include <category/core/bytes.hpp>
    #include <category/core/int.hpp>
    #include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
    #include <category/execution/ethereum/block_hash_buffer.hpp>
    #include <category/execution/ethereum/chain/chain.hpp>
    #include <category/execution/ethereum/core/transaction.hpp>
    #include <category/execution/ethereum/db/trie_db.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/execution/ethereum/domain_anchor.hpp>
    #include <category/execution/ethereum/evmc_host.hpp>
    #include <category/execution/ethereum/execute_message.hpp>
    #include <category/execution/ethereum/state2/block_state.hpp>
    #include <category/execution/ethereum/state3/state.hpp>
    #include <category/execution/ethereum/trace/call_tracer.hpp>
    #include <category/execution/ethereum/tx_context.hpp>
    #include <category/vm/evm/traits.hpp>
    #include <category/vm/vm.hpp>

    #include <evmc/evmc.hpp>

    #include <gtest/gtest.h>

    #include <cstdint>

using namespace monad;

using db_t = TrieDb;

namespace
{
    /// PUSH1 1, PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, RETURN -- canonical ABI
    /// true, which is the only answer that grants access.
    byte_string const ALLOW{
        0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3};
    /// The same with a zero word: a well-formed refusal.
    byte_string const DENY{
        0x60, 0x00, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3};

    constexpr auto CALLER = 0x1111111111111111111111111111111111111111_address;
    constexpr auto TARGET = 0x2222222222222222222222222222222222222222_address;
    constexpr int64_t GAS = 100'000;
    constexpr int64_t STIPEND = 30'000;

    using Trait = EvmTraits<MONAD_ETH_PARIS>;

    evmc_message call_to_target(int64_t const gas = GAS)
    {
        evmc_message msg{};
        msg.kind = EVMC_CALL;
        msg.depth = 0;
        msg.gas = gas;
        msg.recipient = TARGET;
        msg.sender = CALLER;
        msg.code_address = TARGET;
        return msg;
    }
}

struct DomainAccess : public ::testing::Test
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    BlockHashBufferFinalized block_hash_buffer{};
    NoopCallTracer call_tracer{};
    Transaction tx{};
    uint256_t base_fee{0};
    trace::StateTracer noop_state_tracer{std::monostate{}};

    evmc::Result run(byte_string_view const spoke_code)
    {
        state.create_contract(L2_DOMAIN_SPOKE);
        if (!spoke_code.empty()) {
            state.set_code(L2_DOMAIN_SPOKE, spoke_code);
        }
        auto const chain_ctx = ChainContext<Trait>::debug_empty();
        EvmcHost<Trait> host{
            call_tracer,
            noop_state_tracer,
            EMPTY_TX_CONTEXT,
            block_hash_buffer,
            state,
            tx,
            base_fee,
            0,
            chain_ctx};
        auto const msg = call_to_target();
        return execute_call_message<Trait>(&host, state, msg);
    }
};

TEST_F(DomainAccess, ASpokeThatAnswersTrueLetsTheCallThrough)
{
    auto const result = run(ALLOW);
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    // The stipend is charged to the caller, less whatever the check left over,
    // so the call runs with less gas than it asked for -- but never 30,000
    // less, because the check does not spend it all.
    EXPECT_LT(result.gas_left, GAS);
    EXPECT_GT(result.gas_left, GAS - STIPEND);
}

TEST_F(DomainAccess, ASpokeThatAnswersFalseDeniesTheCall)
{
    EXPECT_EQ(run(DENY).status_code, EVMC_REVERT);
}

// Fail closed, which is the half that matters: a spoke that is not there
// answers nothing, and nothing is not true.
TEST_F(DomainAccess, ASpokeWithNoCodeDeniesTheCall)
{
    EXPECT_EQ(run({}).status_code, EVMC_REVERT);
}

// Below the stipend there is nothing to run the check with, and running it
// with less would make the answer depend on the caller's gas.
TEST_F(DomainAccess, ACallBelowTheStipendIsDeniedWithoutAsking)
{
    state.create_contract(L2_DOMAIN_SPOKE);
    state.set_code(L2_DOMAIN_SPOKE, ALLOW);
    auto const chain_ctx = ChainContext<Trait>::debug_empty();
    EvmcHost<Trait> host{
        call_tracer,
        noop_state_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        tx,
        base_fee,
        0,
        chain_ctx};
    auto const msg = call_to_target(STIPEND - 1);
    auto const result = execute_call_message<Trait>(&host, state, msg);
    EXPECT_EQ(result.status_code, EVMC_REVERT);
}

#endif
