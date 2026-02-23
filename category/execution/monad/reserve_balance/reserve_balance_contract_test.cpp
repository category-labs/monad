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
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/vm/code.hpp>
#include <category/vm/compiler.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/vm.hpp>

#include <monad/test/traits_test.hpp>
#include <test/vm/utils/test_message.hpp>

#include <ankerl/unordered_dense.h>
#include <evmc/evmc.h>
#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <limits>

using namespace monad;
using namespace monad::vm;
using enum monad::vm::compiler::EvmOpCode;

enum Outcome
{
    WillRevert,
    WontRevert,
    ContractMissing,
};

struct ReserveBalanceTest : public ::testing::Test
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

struct ReserveBalanceEvm : public ReserveBalanceTest
{
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

void add_revert_if_true(std::vector<uint8_t> &code)
{
    code.append_range(std::initializer_list<uint8_t>{
        PUSH1,
        static_cast<uint8_t>(code.size() + 6),
        JUMPI,
        PUSH1,
        static_cast<uint8_t>(code.size() + 10),
        JUMP,
        JUMPDEST,
        PUSH0,
        PUSH0,
        REVERT,
        JUMPDEST,
    });
}

void add_revert_if_false(std::vector<uint8_t> &code)
{
    code.append_range(std::initializer_list<uint8_t>{
        PUSH1,
        static_cast<uint8_t>(code.size() + 6),
        JUMPI,
        PUSH0,
        PUSH0,
        REVERT,
        JUMPDEST});
}

void add_callee_check(std::vector<uint8_t> &code)
{
    code.append_range(std::initializer_list<uint8_t>{
        PUSH1,
        static_cast<uint8_t>(code.size() + 4),
        JUMPI,
        STOP,
        JUMPDEST,
        0xFE,
    });
}

void add_revert_check(std::vector<uint8_t> &code)
{
    u32_be selector = abi_encode_selector("dippedIntoReserve()");
    auto const *s = selector.bytes;
    auto const *a = intx::as_bytes(RESERVE_BALANCE_CA);
    code.append_range(std::initializer_list<uint8_t>{
        PUSH32, s[0],  s[1],  s[2],  s[3],  0,     0,     0,     0,
        0,      0,     0,     0,     0,     0,     0,     0,     0,
        0,      0,     0,     0,     0,     0,     0,     0,     0,
        0,      0,     0,     0,     0,     0,     PUSH0,
        MSTORE, // store selector

        PUSH1,
        32, // return 1 byte
        PUSH1,
        32, // into offset 32
        PUSH1,
        4, // selector size
        PUSH0, // arg offset
        PUSH0, // no value
        PUSH20, a[0],  a[1],  a[2],  a[3],  a[4],  a[5],  a[6],  a[7],
        a[8],   a[9],  a[10], a[11], a[12], a[13], a[14], a[15], a[16],
        a[17],  a[18], a[19], PUSH1,
        100, // precompile gas cost
        CALL,

        POP,
    });
    code.append_range(std::initializer_list<uint8_t>{
        RETURNDATASIZE,
        PUSH1,
        static_cast<uint8_t>(code.size() + 5),
        JUMPI,
        0xFE,
        JUMPDEST,
        PUSH1,
        32,
        MLOAD,
    });
}

void add_spend_code(uint64_t const value_mon, std::vector<uint8_t> &code)
{
    uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
    auto const *v = intx::as_bytes(value);
    code.append_range(std::initializer_list<uint8_t>{
        PUSH0, PUSH0, PUSH0, PUSH0, PUSH32, v[31], v[30], v[29], v[28], v[27],
        v[26], v[25], v[24], v[23], v[22],  v[21], v[20], v[19], v[18], v[17],
        v[16], v[15], v[14], v[13], v[12],  v[11], v[10], v[9],  v[8],  v[7],
        v[6],  v[5],  v[4],  v[3],  v[2],   v[1],  v[0],  PUSH0, PUSH0, CALL,
    });
}

void add_call_code(
    uint256_t const &gas_fee, Address target, std::vector<uint8_t> &code)
{
    auto const *v = intx::as_bytes(target);
    auto const *g = intx::as_bytes(gas_fee);
    code.append_range(std::initializer_list<uint8_t>{
        PUSH0, PUSH0, PUSH0, PUSH0, PUSH0, PUSH20, v[0],   v[1],  v[2],  v[3],
        v[4],  v[5],  v[6],  v[7],  v[8],  v[9],   v[10],  v[11], v[12], v[13],
        v[14], v[15], v[16], v[17], v[18], v[19],  PUSH32, g[31], g[30], g[29],
        g[28], g[27], g[26], g[25], g[24], g[23],  g[22],  g[21], g[20], g[19],
        g[18], g[17], g[16], g[15], g[14], g[13],  g[12],  g[11], g[10], g[9],
        g[8],  g[7],  g[6],  g[5],  g[4],  g[3],   g[2],   g[1],  g[0],  CALL,
    });
}

template <Traits traits>
    requires is_monad_trait_v<traits>
void run_dipped_into_reserve_test(
    uint64_t const initial_balance_mon, uint64_t const value_mon,
    Outcome outcome)
{
    static constexpr uint256_t GAS_FEE = 4 * 1000000000000000000ULL;
    static constexpr uint256_t BASE_FEE_PER_GAS = 10;
    static constexpr uint256_t GAS_LIMIT = GAS_FEE / BASE_FEE_PER_GAS;
    static constexpr Address BUNDLER{0xbbbbbbbb};
    static constexpr Address ENTRYPOINT{0xeeeeeeee};
    static constexpr Address EOA{0xaaaaaaaa};
    static constexpr Address SCW{0xcccccccc};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    NoopCallTracer call_tracer;
    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized block_hash_buffer{};

    ASSERT_EQ(monad_default_max_reserve_balance_mon(traits::monad_rev()), 10);

    std::vector<uint8_t> scw_code;
    add_spend_code(value_mon, scw_code);

    std::vector<uint8_t> entrypoint_code;
    add_call_code(GAS_FEE / 4, EOA, entrypoint_code);
    add_revert_check(entrypoint_code);
    if (outcome == Outcome::WillRevert) {
        add_revert_if_true(entrypoint_code);
    }

    // Set up initial state
    {
        State state{bs, Incarnation{0, 0}};
        uint256_t const initial_balance =
            uint256_t{initial_balance_mon} * 1000000000000000000ULL;
        state.add_to_balance(EOA, initial_balance);

        // set EOA to delegate to SCW
        evmc::bytes const delegate_code =
            evmc::from_hex(std::format("0xef0100{}", evmc::hex(SCW))).value();
        state.set_code(EOA, byte_string_view{delegate_code});

        state.create_contract(SCW);
        state.set_code(SCW, byte_string_view{scw_code});

        state.create_contract(ENTRYPOINT);
        state.set_code(ENTRYPOINT, byte_string_view{entrypoint_code});

        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
    }

    Transaction const tx{
        .max_fee_per_gas = BASE_FEE_PER_GAS,
        .gas_limit = uint64_t{GAS_LIMIT},
        .type = TransactionType::legacy,
        .max_priority_fee_per_gas = 0,
    };

    std::vector<Address> senders;
    senders.push_back(BUNDLER);
    senders.emplace_back(BUNDLER);
    std::vector<std::vector<std::optional<Address>>> authorities = {};
    authorities.push_back({});
    authorities.push_back({});

    // Create sets for the new MonadChainContext structure
    ankerl::unordered_dense::segmented_set<Address>
        grandparent_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address>
        parent_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> const
        senders_and_authorities = {EOA};
    ChainContext<traits> chain_context{
        .grandparent_senders_and_authorities =
            grandparent_senders_and_authorities,
        .parent_senders_and_authorities = parent_senders_and_authorities,
        .senders_and_authorities = senders_and_authorities,
        .senders = senders,
        .authorities = authorities};

    {
        State state{bs, Incarnation{1, 1}};

        EvmcHost<traits> host{
            call_tracer,
            tx_context,
            block_hash_buffer,
            state,
            tx,
            BASE_FEE_PER_GAS,
            1,
            chain_context};

        monad::vm::test::TestMessage test_msg_;
        evmc_message msg{*test_msg_};
        msg.gas = int64_t{GAS_LIMIT}, msg.recipient = ENTRYPOINT;
        msg.sender = BUNDLER;

        init_reserve_balance_context<traits>(
            state,
            msg.sender,
            tx,
            host.base_fee_per_gas_,
            host.i_,
            host.chain_ctx_);

        auto const &code_hash =
            to_bytes(keccak256(byte_string_view{entrypoint_code}));
        auto icode =
            make_shared_intercode(std::span<uint8_t const>{entrypoint_code});

        evmc_status_code expected;
        switch (outcome) {
        case WillRevert:
            expected = EVMC_REVERT;
            break;
        case WontRevert:
            expected = EVMC_SUCCESS;
            break;
        case ContractMissing:
            expected = EVMC_FAILURE;
            break;
        }

        auto result = vm.execute<traits>(
            host, &msg, code_hash, make_shared<Varcode>(icode));
        EXPECT_EQ(expected, result.status_code);
    }
}

EXPLICIT_MONAD_TRAITS(run_dipped_into_reserve_test);

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

    init_reserve_balance_context<MonadTraits<MONAD_NEXT>>(
        state,
        Address{m.sender},
        empty_tx,
        h.base_fee_per_gas_,
        h.i_,
        h.chain_ctx_);

    auto const result = h.call(m);
    EXPECT_EQ(result.status_code, EVMC_REVERT);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.gas_refund, 0);
    EXPECT_EQ(result.output_size, 20);

    auto const message = std::string_view{
        reinterpret_cast<char const *>(result.output_data), 20};
    EXPECT_EQ(message, "method not supported");
}

TYPED_TEST(MonadTraitsTest, reverttransaction_no_dip)
{
    constexpr Outcome outcome = [] {
        if (TestFixture::Trait::monad_rev() >= MONAD_NEXT) {
            return Outcome::WontRevert;
        }
        else {
            return Outcome::ContractMissing;
        }
    }();

    run_dipped_into_reserve_test<typename TestFixture::Trait>(10, 0, outcome);
}

TYPED_TEST(MonadTraitsTest, reverttransaction_revert)
{
    constexpr Outcome outcome = [] {
        if (TestFixture::Trait::monad_rev() >= MONAD_NEXT) {
            return Outcome::WillRevert;
        }
        else {
            return Outcome::ContractMissing;
        }
    }();

    run_dipped_into_reserve_test<typename TestFixture::Trait>(15, 11, outcome);
}
