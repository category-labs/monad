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

#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/vm/code.hpp>
#include <category/vm/compiler.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>

#include <monad/test/traits_test.hpp>

#include <test_resource_data.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <evmone/baseline.hpp>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <ranges>
#include <vector>

#include <quill/Quill.h>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>

using namespace monad;
using namespace monad::vm;
using enum monad::vm::compiler::EvmOpCode;

/*

- 1 * | 2 over -> 2 reverts

1 over | 2 over | 2 c&r

false: ← | true: → 

                 1 over
          /                    \
        2 over                 2 over
     /         \             /         \
  2 cr        2 cr        2 cr        2 cr
  /  \        

  2r: 0       2r: 1       2r:         2r:
  1cr: rev    1cr: suc    1cr:        2cr:

*/

void add_revert_if_true(std::vector<uint8_t> &code)
{
    code.append_range(std::initializer_list<uint8_t>{
        PUSH1, static_cast<uint8_t>(code.size() + 6), JUMPI,
        PUSH1, static_cast<uint8_t>(code.size() + 10), JUMP,
        JUMPDEST, PUSH0, PUSH0, REVERT,
        JUMPDEST,
    });
}

void add_revert_if_false(std::vector<uint8_t> &code)
{
    code.append_range(std::initializer_list<uint8_t>{
        PUSH1, static_cast<uint8_t>(code.size() + 6), JUMPI,
        PUSH0, PUSH0, REVERT,
        JUMPDEST
    });
}

void add_callee_check(std::vector<uint8_t> &code)
{
    code.append_range(std::initializer_list<uint8_t>{
        PUSH1, static_cast<uint8_t>(code.size() + 4), JUMPI, STOP, JUMPDEST, 0xFE,
    });
}

void add_call_code(uint256_t const &gas_fee, Address target, std::vector<uint8_t> &code)
{
    auto const *v = intx::as_bytes(target);
    auto const *g = intx::as_bytes(gas_fee);
    code.append_range(std::initializer_list<uint8_t>{
        PUSH0, PUSH0, PUSH0, PUSH0, PUSH0,
        PUSH20,
        v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18], v[19],
        PUSH32,
        g[31], g[30], g[29], g[28], g[27], g[26], g[25], g[24],
        g[23], g[22], g[21], g[20], g[19], g[18], g[17], g[16],
        g[15], g[14], g[13], g[12], g[11], g[10], g[9], g[8],
        g[7], g[6], g[5], g[4], g[3], g[2], g[1], g[0],  // TODO(GAS)
        CALL,
    });
}

void add_spend_code(uint64_t const value_mon, std::vector<uint8_t> &code)
{
    uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
    auto const *v = intx::as_bytes(value);
    code.append_range(std::initializer_list<uint8_t>{
        PUSH0, PUSH0, PUSH0, PUSH0,
        PUSH32,
        v[31], v[30], v[29], v[28], v[27], v[26], v[25], v[24],
        v[23], v[22], v[21], v[20], v[19], v[18], v[17], v[16],
        v[15], v[14], v[13], v[12], v[11], v[10], v[9], v[8],
        v[7], v[6], v[5], v[4], v[3], v[2], v[1], v[0], 
        PUSH0, PUSH0, CALL,
    });
}

enum Outcome
{
    ShouldSucceed,
    ShouldRevert,
    ShouldFail,
};

template <Traits traits>
    requires is_monad_trait_v<traits>
void run_revert_transaction_test(
                                 uint64_t const initial_balance_mon, uint64_t const value_mon, Outcome outcome)
{
    constexpr uint256_t GAS_FEE = 4 * 1000000000000000000ULL;
    constexpr uint256_t BASE_FEE_PER_GAS = 10;
    constexpr uint256_t GAS_LIMIT = GAS_FEE / BASE_FEE_PER_GAS;
    constexpr Address BUNDLER{0xbbbbbbbb};
    (void)BUNDLER;
    constexpr Address ENTRYPOINT{0xeeeeeeee};
    constexpr Address EOA{0xaaaaaaaa};
    constexpr Address SCW{0xcccccccc};

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
    (void)value_mon;
    add_spend_code(value_mon, scw_code);
    // scw_code.push_back(0xFE);
    // add_reserve_check(scw_code);
    // scw_code.push_back(CHECKRESERVEBALANCE);

    std::vector<uint8_t> entrypoint_code;
    add_call_code(GAS_FEE / 4, EOA, entrypoint_code);
    entrypoint_code.push_back(CHECKRESERVEBALANCE);
    if (outcome == ShouldRevert) {
        add_revert_if_true(entrypoint_code);
    }
    else if (outcome == ShouldSucceed) {
        add_revert_if_false(entrypoint_code);
    }

    // Set up initial state
    {
        State state{bs, Incarnation{0, 0}};
        uint256_t const initial_balance =
            uint256_t{initial_balance_mon} * 1000000000000000000ULL;
        state.add_to_balance(EOA, initial_balance);

        auto const *a = intx::as_bytes(SCW);
        state.set_code(EOA, byte_string_view{std::initializer_list<uint8_t>{
            0xef, 0x01, 0x00,
            a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15], a[16], a[17], a[18], a[19], 
        }});

        // auto const &scw_code_hash = to_bytes(keccak256(byte_string_view{scw_code}));
        // LOG_ERROR("scw_code_hash: 0x{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        // scw_code_hash.bytes[31], scw_code_hash.bytes[30], scw_code_hash.bytes[29], scw_code_hash.bytes[28], scw_code_hash.bytes[27], scw_code_hash.bytes[26], scw_code_hash.bytes[25], scw_code_hash.bytes[24],
        // scw_code_hash.bytes[23], scw_code_hash.bytes[22], scw_code_hash.bytes[21], scw_code_hash.bytes[20], scw_code_hash.bytes[19], scw_code_hash.bytes[18], scw_code_hash.bytes[17], scw_code_hash.bytes[16],
        // scw_code_hash.bytes[15], scw_code_hash.bytes[14], scw_code_hash.bytes[13], scw_code_hash.bytes[12], scw_code_hash.bytes[11], scw_code_hash.bytes[10], scw_code_hash.bytes[9], scw_code_hash.bytes[8],
        // scw_code_hash.bytes[7], scw_code_hash.bytes[6], scw_code_hash.bytes[5], scw_code_hash.bytes[4], scw_code_hash.bytes[3], scw_code_hash.bytes[2], scw_code_hash.bytes[1], scw_code_hash.bytes[0]);
        state.create_contract(SCW);
        state.set_code(SCW, byte_string_view{scw_code});

        // auto const &entrypoint_code_hash = to_bytes(keccak256(byte_string_view{entrypoint_code}));
        // LOG_ERROR("entrypoint_code_hash: 0x{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        // entrypoint_code_hash.bytes[31], entrypoint_code_hash.bytes[30], entrypoint_code_hash.bytes[29], entrypoint_code_hash.bytes[28], entrypoint_code_hash.bytes[27], entrypoint_code_hash.bytes[26], entrypoint_code_hash.bytes[25], entrypoint_code_hash.bytes[24],
        // entrypoint_code_hash.bytes[23], entrypoint_code_hash.bytes[22], entrypoint_code_hash.bytes[21], entrypoint_code_hash.bytes[20], entrypoint_code_hash.bytes[19], entrypoint_code_hash.bytes[18], entrypoint_code_hash.bytes[17], entrypoint_code_hash.bytes[16],
        // entrypoint_code_hash.bytes[15], entrypoint_code_hash.bytes[14], entrypoint_code_hash.bytes[13], entrypoint_code_hash.bytes[12], entrypoint_code_hash.bytes[11], entrypoint_code_hash.bytes[10], entrypoint_code_hash.bytes[9], entrypoint_code_hash.bytes[8],
        // entrypoint_code_hash.bytes[7], entrypoint_code_hash.bytes[6], entrypoint_code_hash.bytes[5], entrypoint_code_hash.bytes[4], entrypoint_code_hash.bytes[3], entrypoint_code_hash.bytes[2], entrypoint_code_hash.bytes[1], entrypoint_code_hash.bytes[0]);
        state.create_contract(ENTRYPOINT);
        state.set_code(ENTRYPOINT, byte_string_view{entrypoint_code});

        // state.add_to_balance(ONE, initial_balance);
        // state.add_to_balance(TWO, initial_balance - 1);

        // std::vector<uint8_t> two_code;
        // two_code.append_range(std::initializer_list<uint8_t>{
        //     PUSH0, PUSH0, PUSH0, PUSH0, PUSH0,
        //     PUSH1, 0xFF, PUSH4, 0xFF, 0xFF, 0xFF, 0xFF,
        //     CALL
        // });
        // (void)value_mon;
        // two_code.push_back(CHECKRESERVEBALANCE);
        // add_spend_code(value_mon, two_code);
        // two_code.push_back(CHECKRESERVEBALANCE);
        // state.create_contract(TWO);
        // state.set_code(TWO, byte_string_view{two_code});
        // state.set_nonce(TWO, 0x0);

        // auto hash = state.get_code_hash(SCW);
        // LOG_ERROR("get_code_hash(SCW): 0x{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        // hash.bytes[31], hash.bytes[30], hash.bytes[29], hash.bytes[28], hash.bytes[27], hash.bytes[26], hash.bytes[25], hash.bytes[24],
        // hash.bytes[23], hash.bytes[22], hash.bytes[21], hash.bytes[20], hash.bytes[19], hash.bytes[18], hash.bytes[17], hash.bytes[16],
        // hash.bytes[15], hash.bytes[14], hash.bytes[13], hash.bytes[12], hash.bytes[11], hash.bytes[10], hash.bytes[9], hash.bytes[8],
        // hash.bytes[7], hash.bytes[6], hash.bytes[5], hash.bytes[4], hash.bytes[3], hash.bytes[2], hash.bytes[1], hash.bytes[0]);

        // hash = to_bytes(keccak256(byte_string_view{std::initializer_list<uint8_t>{}}));
        // LOG_ERROR("hash(0): 0x{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        // hash.bytes[31], hash.bytes[30], hash.bytes[29], hash.bytes[28], hash.bytes[27], hash.bytes[26], hash.bytes[25], hash.bytes[24],
        // hash.bytes[23], hash.bytes[22], hash.bytes[21], hash.bytes[20], hash.bytes[19], hash.bytes[18], hash.bytes[17], hash.bytes[16],
        // hash.bytes[15], hash.bytes[14], hash.bytes[13], hash.bytes[12], hash.bytes[11], hash.bytes[10], hash.bytes[9], hash.bytes[8],
        // hash.bytes[7], hash.bytes[6], hash.bytes[5], hash.bytes[4], hash.bytes[3], hash.bytes[2], hash.bytes[1], hash.bytes[0]);

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
        // LOG_ERROR("expected: {}", evmc::to_string(expected));
        // LOG_ERROR("initial balance: {}", state.get_balance(ONE));
        // state.subtract_from_balance(ONE, gas_fee);
        // LOG_ERROR("gas balance    : {}", state.get_balance(ONE));
        // uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
        // state.subtract_from_balance(ONE, value);

        EvmcHost<traits> host{
            call_tracer,
            tx_context,
            block_hash_buffer,
            state,
            EOA,
            tx,
            BASE_FEE_PER_GAS,
            1,
            chain_context};

        // std::vector<uint8_t> one_code;
        // add_spend_code(value_mon, one_code);
        // add_reserve_check(one_code);
        // add_call_code(TWO, one_code);
        // add_reserve_check(one_code);
        // std::span<uint8_t const> code{one_code};

        // std::span<uint8_t const> code{{PUSH0, PUSH0, PUSH0, PUSH0,
        //     PUSH32,
        //     v[31], v[30], v[29], v[28], v[27], v[26], v[25], v[24],
        //     v[23], v[22], v[21], v[20], v[19], v[18], v[17], v[16],
        //     v[15], v[14], v[13], v[12], v[11], v[10], v[9], v[8],
        //     v[7], v[6], v[5], v[4], v[3], v[2], v[1], v[0], 
        //     PUSH0, PUSH0, CALL,
        //     CHECKRESERVEBALANCE, PUSH1, 45, JUMPI, STOP, JUMPDEST, PUSH1, 0, PUSH1, 0, REVERT,
        // }};



        // std::span<uint8_t const> code{{PUSH0, PUSH0, PUSH0, PUSH0,
        //     PUSH8, 
        //     0x53, 0x44, 0x48, 0x35, 0xec, 0x58, 0x00, 0x00,
        //     PUSH0, PUSH0, CALL,
        //     PUSH1, 20, JUMPI, 0xFE, JUMPDEST, CHECKRESERVEBALANCE,
        // }};

        // std::span<uint8_t const> code{{CHECKRESERVEBALANCE, PUSH1, 5, JUMPI, STOP, JUMPDEST, PUSH1, 0, PUSH1, 0, REVERT}};

        std::span<uint8_t const> code{entrypoint_code};

        auto const &code_hash = to_bytes(keccak256(byte_string_view{code.data(), code.size()}));

        evmc_message const msg{
            .kind = EVMC_CALL,
            .flags = 0,
            .depth = 0,
            .gas = int64_t{GAS_LIMIT},
            .recipient = ENTRYPOINT,
            .sender = BUNDLER,
            .input_data = nullptr,
            .input_size = 0,
            .value = {0},
            .create2_salt = {},
            .code_address = ENTRYPOINT,
            .memory_handle = nullptr,
            .memory = nullptr,
            .memory_capacity = 0,
        };

        auto icode = make_shared_intercode(code);

        auto result = vm.execute<traits>(host, &msg, code_hash, make_shared<Varcode>(icode));
        evmc_status_code expected = (outcome == ShouldSucceed || outcome == ShouldRevert)
                                    ? EVMC_REVERT
                                    : EVMC_FAILURE;
        EXPECT_EQ(expected, result.status_code);

        // auto ncode = vm.compiler().compile<traits>(icode);
        // ASSERT_TRUE(ncode->entrypoint() != nullptr);

        // result = vm.execute<traits>(host, &msg, code_hash, make_shared<Varcode>(icode, ncode));
        // EXPECT_EQ(expected, result.status_code);

        // LOG_ERROR("final balance  : {}\n", state.get_balance(ONE));
        // LOG_ERROR("\n");
    }
}

EXPLICIT_MONAD_TRAITS(run_revert_transaction_test)

TYPED_TEST(
    MonadTraitsTest, reverttransaction_no_dip)
{
    constexpr Outcome expected = [] {
        if (TestFixture::Trait::monad_rev() >= MONAD_NEXT) {
            return ShouldSucceed;
        }
        else {
            return ShouldFail;
        }
    }();
    
    run_revert_transaction_test<typename TestFixture::Trait>(10, 0, expected);
}

TYPED_TEST(
    MonadTraitsTest, reverttransaction_revert)
{
    constexpr Outcome expected = [] {
        if (TestFixture::Trait::monad_rev() >= MONAD_NEXT) {
            return ShouldRevert;
        }
        else {
            return ShouldFail;
        }
    }();
    
    run_revert_transaction_test<typename TestFixture::Trait>(15, 11, expected);
}
