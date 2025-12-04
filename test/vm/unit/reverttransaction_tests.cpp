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

using namespace monad;
using namespace monad::vm;
using enum monad::vm::compiler::EvmOpCode;

template <Traits traits>
    requires is_monad_trait_v<traits>
void run_revert_transaction_test(
    uint64_t const initial_balance_mon,
    uint64_t const gas_fee_mon, uint64_t const value_mon, evmc_status_code const expected)
{
    constexpr uint256_t BASE_FEE_PER_GAS = 10;
    constexpr Address SENDER{1};
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    NoopCallTracer call_tracer;
    evmc_tx_context const tx_context{};
    BlockHashBufferFinalized block_hash_buffer{};

    ASSERT_EQ(monad_default_max_reserve_balance_mon(traits::monad_rev()), 10);

    // Set up initial state
    {
        State state{bs, Incarnation{0, 0}};
        uint256_t const initial_balance =
            uint256_t{initial_balance_mon} * 1000000000000000000ULL;
        state.add_to_balance(SENDER, initial_balance);
        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
    }

    uint256_t const gas_fee = uint256_t{gas_fee_mon} * 1000000000000000000ULL;
    uint256_t const gas_limit = gas_fee / BASE_FEE_PER_GAS;
    MONAD_ASSERT(
        (gas_fee % BASE_FEE_PER_GAS) == 0 &&
        gas_limit <= std::numeric_limits<uint64_t>::max());

    Transaction const tx{
        .max_fee_per_gas = BASE_FEE_PER_GAS,
        .gas_limit = uint64_t{gas_limit},
        .type = TransactionType::legacy,
        .max_priority_fee_per_gas = 0,
    };

    std::vector<Address> senders;
    senders.push_back(SENDER);
    senders.emplace_back(SENDER);
    std::vector<std::vector<std::optional<Address>>> authorities = {};
    authorities.push_back({});
    authorities.push_back({});

    // Create sets for the new MonadChainContext structure
    ankerl::unordered_dense::segmented_set<Address>
        grandparent_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address>
        parent_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> const
        senders_and_authorities = {SENDER};

    ChainContext<traits> chain_context{
        .grandparent_senders_and_authorities =
            grandparent_senders_and_authorities,
        .parent_senders_and_authorities = parent_senders_and_authorities,
        .senders_and_authorities = senders_and_authorities,
        .senders = senders,
        .authorities = authorities};

    {
        State state{bs, Incarnation{1, 1}};
        state.subtract_from_balance(SENDER, gas_fee);
        uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
        state.subtract_from_balance(SENDER, value);

        EvmcHost<traits> host{
            call_tracer,
            tx_context,
            block_hash_buffer,
            state,
            SENDER,
            tx,
            BASE_FEE_PER_GAS,
            1,
            chain_context};

        evmc_message msg{};
        msg.gas = int64_t{gas_limit};
        msg.sender = SENDER;

        std::span<std::uint8_t const> code{{CHECKRESERVEBALANCE, PUSH1, 5, JUMPI, STOP, JUMPDEST, PUSH1, 0, PUSH1, 0, REVERT}};

        auto rt_ctx = runtime::Context::from(
            runtime::EvmMemoryAllocator{},
            &host.get_interface(),
            host.to_context(),
            &msg,
            code);

        auto icode = make_shared_intercode(code);

        auto result =
            vm.execute_intercode_raw<traits>(rt_ctx, icode);

        EXPECT_EQ(expected, result.status_code);

        auto ncode = vm.compiler().compile<traits>(icode);
        ASSERT_TRUE(ncode->entrypoint() != nullptr);

        result = evmc::Result{vm.execute_native_entrypoint_raw(
                                                                rt_ctx, ncode->entrypoint())};

        EXPECT_EQ(expected, result.status_code);
    }
}

EXPLICIT_MONAD_TRAITS(run_revert_transaction_test)

// template <Traits traits>
// void run_revert_transaction_test(
//     uint64_t const initial_balance_mon,
//     uint64_t const value_mon, evmc_status_code const expected)
// {
//     constexpr uint256_t BASE_FEE_PER_GAS = 10;
//     constexpr Address SENDER{1};
//     constexpr Address CONTRACT{2};

//     uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;

//     InMemoryMachine machine;
//     mpt::Db db{machine};
//     TrieDb tdb{db};
//     vm::VM vm;
//     BlockState bs{tdb, vm};
//     BlockMetrics metrics;
//     NoopCallTracer call_tracer;
//     trace::StateTracer state_tracer;

//     {
//         (void) value;
//         // auto const *v = intx::as_bytes(value);
//         // std::span<std::uint8_t const> contract{{
//         //     PUSH1, 0, PUSH1, 0, PUSH1, 0, PUSH1, 0,
//         //     PUSH32,
//         //     v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7],
//         //     v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15],
//         //     v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23],
//         //     v[24], v[25], v[26], v[27], v[28], v[29], v[30], v[31],
//         //     PUSH1, 0x0, PUSH1, 0, CALL,
//         //     CHECKRESERVEBALANCE, PUSH1, 51, JUMPI, STOP, JUMPDEST, REVERT}};
//         // std::span<std::uint8_t const> contract{{
//         //     PUSH1, 0, PUSH1, 0, PUSH1, 0, PUSH1, 0,
//         //     PUSH32,
//         //     v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7],
//         //     v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15],
//         //     v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23],
//         //     v[24], v[25], v[26], v[27], v[28], v[29], v[30], v[31],
//         //     PUSH1, 0x0, PUSH1, 0, CALL}};
//         std::span<std::uint8_t const> contract{{STOP}};
//         auto code = byte_string_view{contract.data(), contract.size()};

//         State init_state{bs, Incarnation{0, 0}};

//         init_state.create_contract(CONTRACT);

//         init_state.set_code(CONTRACT, code);

//         uint256_t const initial_balance =
//             uint256_t{initial_balance_mon} * 1000000000000000000ULL;
//         init_state.add_to_balance(SENDER, initial_balance);
//         ASSERT_TRUE(bs.can_merge(init_state));
//         bs.merge(init_state);
//     }

//     Transaction tx{
//         .sc = SignatureAndChain{.r = 1, .s = 1}, // TODO: different chains?
//         .nonce = 1,
//         .max_fee_per_gas = BASE_FEE_PER_GAS,
//         .gas_limit = std::numeric_limits<uint64_t>::max(),
//         .value = 0,
//         .to = CONTRACT,
//         .type = TransactionType::legacy,
//         .max_priority_fee_per_gas = BASE_FEE_PER_GAS,
//         .max_fee_per_blob_gas = 0,
//         .blob_versioned_hashes = {}
//     };

//     std::vector<Address> senders = {SENDER};
//     std::vector<std::vector<std::optional<Address>>> authorities = {};
//     authorities.push_back({});
 
//     // Create sets for the new MonadChainContext structure
//     ankerl::unordered_dense::segmented_set<Address>
//         grandparent_senders_and_authorities;
//     ankerl::unordered_dense::segmented_set<Address>
//         parent_senders_and_authorities;
//     ankerl::unordered_dense::segmented_set<Address> const
//         senders_and_authorities = {SENDER};

//     MonadChainContext chain_context{
//         .grandparent_senders_and_authorities =
//             &grandparent_senders_and_authorities,
//         .parent_senders_and_authorities = &parent_senders_and_authorities,
//         .senders_and_authorities = senders_and_authorities,
//         .senders = senders,
//         .authorities = authorities};

//     auto prev = boost::fibers::promise<void>();
//     prev.set_value();

//     auto const receipt =
//         ExecuteTransaction<traits>(
//             MonadMainnet{}, // TODO: different chains?
//             0,
//             tx,
//             SENDER,
//             {},
//             BlockHeader{},
//             BlockHashBufferFinalized{},
//             bs,
//             metrics,
//             prev,
//             call_tracer,
//             state_tracer,
//             [&BASE_FEE_PER_GAS, &chain_context](Address const &sender,
//                                                 Transaction const &tx,
//                                                 uint64_t const i,
//                                                 State &state) {
//                 return revert_monad_transaction<traits>(sender,
//                                                         tx,
//                                                         BASE_FEE_PER_GAS,
//                                                         i,
//                                                         state,
//                                                         chain_context);
//             }
//         )();

//     ASSERT_TRUE(receipt);
//     ASSERT_EQ(receipt.value().status, expected); 
// }

// EXPLICIT_MONAD_TRAITS(run_revert_transaction_test);

TYPED_TEST(
    MonadTraitsTest, reverttransaction_no_dip)
{
    constexpr evmc_status_code expected = [] {
        if (TestFixture::Trait::monad_rev() >= MONAD_NEXT) {
            return EVMC_SUCCESS;
        }
        else {
            return EVMC_FAILURE;
        }
    }();
    
    run_revert_transaction_test<typename TestFixture::Trait>(10, 1, 0, expected);
}

TYPED_TEST(
    MonadTraitsTest, reverttransaction_revert)
{
    constexpr evmc_status_code expected = [] {
        if (TestFixture::Trait::monad_rev() >= MONAD_NEXT) {
            return EVMC_REVERT;
        }
        else {
            return EVMC_FAILURE;
        }
    }();
    
    run_revert_transaction_test<typename TestFixture::Trait>(15, 5, 6, expected);
}

// // using monad::EvmTraits;
// // using namespace monad::vm;
// // using namespace monad::vm::compiler;
// // using namespace monad::vm::compiler::test;

// // TYPED_TEST(VMTraitsTest, Stop)
// // {
// //     TestFixture::execute(0, {STOP});
// //     ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// // }

// // TYPED_TEST(VMTraitsTest, Push0)
// // {
// //     TestFixture::execute(2, {PUSH0});
// //     // PUSH0 supported since EIP-3855
// //     if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SHANGHAI) {
// //         ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// //     }
// //     else {
// //         ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
// //     }
// //     ASSERT_EQ(this->result_.gas_left, 0);
// // }

// // TYPED_TEST(VMTraitsTest, PushSeveral)
// // {
// //     if constexpr (TestFixture::Trait::evm_rev() < EVMC_SHANGHAI) {
// //         TestFixture::execute(11, {PUSH1, 0x01, PUSH2, 0x20, 0x20, PUSH1, 0x0});
// //     }
// //     else {
// //         TestFixture::execute(10, {PUSH1, 0x01, PUSH2, 0x20, 0x20, PUSH0});
// //     }
// //     ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// //     ASSERT_EQ(this->result_.gas_left, 2);
// // }

// // TYPED_TEST(VMTraitsTest, OutOfGas) {
// //     TestFixture::execute(8, {PUSH1, 0x0, PUSH1, 0x0, ADD});
// //     ASSERT_EQ(this->result_.status_code, EVMC_OUT_OF_GAS);
// //     ASSERT_EQ(this->result_.gas_left, 0);
// // }

// // // https://github.com/category-labs/monad-compiler/issues/138
// // TYPED_TEST(VMTraitsTest, BeaconRootRegression_138)
// // {
// //     using namespace evmc::literals;

// //     this->msg_.sender = 0xbe862ad9abfe6f22bcb087716c7d89a26051f74c_address;

// //     auto insts = std::vector<std::uint8_t>{{CALLER, PUSH20}};

// //     for (auto b : this->msg_.sender.bytes) {
// //         insts.push_back(b);
// //     }

// //     for (auto b : std::vector<std::uint8_t>{
// //              EQ, PUSH1, 0x1D, JUMPI, PUSH0, PUSH0, REVERT, JUMPDEST, STOP}) {
// //         insts.push_back(b);
// //     }

// //     ASSERT_EQ(insts[2], 0xBE);
// //     ASSERT_EQ(insts[21], 0x4C);
// //     TestFixture::execute(insts);

// //     ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// // }

// // // https://github.com/category-labs/monad-compiler/issues/190
// // TYPED_TEST(VMTraitsTest, UnderflowRegression_190)
// // {
// //     TestFixture::execute({POP});
// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
// // }

// // // https://github.com/category-labs/monad-compiler/issues/192
// // TYPED_TEST(VMTraitsTest, BadJumpRegression_192)
// // {
// //     TestFixture::execute({PUSH0, JUMP});
// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
// // }

// // TEST_P(VMFileTest, RegressionFile)
// // {
// //     auto const [entry, rev] = GetParam();

// //     // TODO: this test is disabled for MONAD_SEVEN onward until evmone has a
// //     // monad revision and can execute with the same gas costs as MONAD_SEVEN
// //     if (rev >= std::variant<evmc_revision, monad_revision>{MONAD_SEVEN}) {
// //         return;
// //     }
// //     auto file = std::ifstream{entry.path(), std::ifstream::binary};

// //     ASSERT_TRUE(file.good());

// //     std::vector<uint8_t> code(std::istreambuf_iterator<char>{file}, {});

// //     execute_and_compare(30'000'000, code, rev);
// // }

// // TYPED_TEST(VMTraitsTest, SignextendLiveIndexBug)
// // {
// //     TestFixture::execute(
// //         100,
// //         {GAS,
// //          DUP1,
// //          SIGNEXTEND,
// //          PUSH1,
// //          0x0,
// //          MSTORE,
// //          PUSH1,
// //          32,
// //          PUSH1,
// //          0x0,
// //          RETURN});
// //     ASSERT_EQ(this->result_.output_size, 32);
// //     ASSERT_EQ(
// //         uint256_t::load_be_unsafe(this->result_.output_data), uint256_t{98});
// // }

// // TYPED_TEST(VMTraitsTest, JumpiLiveDestDeferredComparisonBug)
// // {
// //     TestFixture::execute(
// //         1000,
// //         {JUMPDEST,
// //          GAS,
// //          ADDRESS,
// //          ADD,
// //          PUSH1,
// //          0xf9,
// //          SHL,
// //          ADDRESS,
// //          ADDRESS,
// //          SLT,
// //          JUMPI});
// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
// // }

// // TYPED_TEST(VMTraitsTest, Cmov32BitBug)
// // {
// //     TestFixture::execute(
// //         1000,
// //         {PUSH1,
// //          0x60,
// //          PUSH1,
// //          0x02,
// //          EXP,
// //          PUSH1,
// //          0x30,
// //          DUP2,
// //          SAR,
// //          ADDRESS,
// //          JUMPI});
// //     if constexpr (TestFixture::Trait::evm_rev() >= EVMC_CONSTANTINOPLE) {
// //         // SAR opcode only available since EIP-145
// //         ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// //     }
// //     else {
// //         ASSERT_NE(this->result_.status_code, EVMC_SUCCESS);
// //     }
// // }

// // TYPED_TEST(VMTraitsTest, MissingDischargeInJumpiKeepFallthroughStack)
// // {
// //     std::vector<uint8_t> bytecode{
// //         0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x00, 0x38, 0x57,
// //         0x80, 0xfd, 0x5b, 0x50, 0x61, 0x01, 0xf7, 0x80, 0x61, 0x00, 0x1c, 0x5f,
// //         0x39, 0x5f, 0xf3, 0xfe, 0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15,
// //         0x61, 0x00, 0x0f, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36,
// //         0x10, 0x61, 0x00, 0x34, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63,
// //         0xb3, 0xde, 0x64, 0x8b, 0x14, 0x61, 0x0e, 0x57, 0x5f, 0x80, 0x63, 0xe4,
// //         0x20, 0x26, 0x4a, 0x14, 0x61, 0x00, 0x6a, 0x57, 0x5b, 0x5f, 0x80, 0xfd,
// //         0x5b, 0x61, 0x00, 0x52, 0x60, 0x04, 0x80, 0x36, 0x03, 0x81, 0x01, 0x90,
// //         0x61, 0x00, 0x4d, 0x91, 0x90, 0x61, 0x01, 0x52, 0x56, 0x5b, 0x61, 0x00,
// //         0x9c, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x61, 0x00, 0x61, 0x93, 0x92, 0x91,
// //         0x90, 0x61, 0x01, 0x8c, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x81, 0x90, 0x39,
// //         0x0f, 0x35, 0x5b, 0x61, 0x00, 0x84, 0x60, 0x04, 0x80, 0x36, 0x03, 0x81,
// //         0x01, 0x90, 0x61, 0x00, 0x7f, 0x91, 0x90, 0x61, 0x01, 0x52, 0x56, 0x5b,
// //         0x61, 0x00, 0xdb, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x61, 0x00, 0x93, 0x93,
// //         0x92, 0x91, 0x90, 0x61, 0x01, 0x8c, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x81,
// //         0x90, 0x39, 0x0f, 0x35, 0x5b, 0x5f, 0x80, 0x5f, 0x80, 0x60, 0xf8, 0x85,
// //         0x90, 0x1b, 0x90, 0x50, 0x80, 0x5f, 0x1a, 0x90, 0x50, 0x5f, 0x60, 0x08,
// //         0x86, 0x90, 0x1b, 0x90, 0x50, 0x80, 0x60, 0x1e, 0x1a, 0x90, 0x50, 0x5f,
// //         0x60, 0x10, 0x87, 0x90, 0x1b, 0x90, 0x50, 0x80, 0x60, 0x11, 0x1a, 0x90,
// //         0x50, 0x82, 0x82, 0x82, 0x95, 0x50, 0x95, 0x50, 0x1b, 0x90, 0x50, 0x80,
// //         0x5f, 0x1a, 0x90, 0x5a, 0x5f, 0x60, 0x08, 0x86, 0x90, 0x1b, 0x90, 0x50,
// //         0x85, 0x90, 0x1c, 0x90, 0x50, 0x80, 0x60, 0x1f, 0x1a, 0x90, 0x50, 0x5f,
// //         0x60, 0x08, 0x86, 0x90, 0x1c, 0x90, 0x50, 0x80, 0x60, 0x04, 0x1a, 0x90,
// //         0x50, 0x5f, 0x60, 0x10};
// //     TestFixture::execute_and_compare(1'000'000, bytecode, {});
// // }

// // TYPED_TEST(VMTraitsTest, WrongGasCheckConditionalJump)
// // {
// //     std::vector<uint8_t> bytecode{
// //         0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
// //         0x80, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
// //         0x35, 0x60, 0xe0, 0x06, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e,
// //         0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26,
// //         0x57, 0x5f, 0x35, 0x60, 0xe0, 0x01, 0xc8, 0x80, 0x63, 0x26, 0x12, 0x1f,
// //         0xf0, 0x14, 0x60, 0x2a, 0x57, 0xb5, 0x5f, 0x80, 0xfd, 0x5b, 0x60, 0x30,
// //         0x60, 0x32, 0x56, 0x5b, 0x00, 0x5b, 0x56, 0xfe, 0xa2, 0x64, 0x69, 0x78,
// //         0x06, 0x73, 0x58, 0x22, 0x12, 0x20, 0xaa, 0xfb, 0xea, 0x54, 0x7b, 0x5a,
// //         0x65, 0x1b, 0x3b, 0x1a, 0x08, 0x4f, 0xb0, 0xbb, 0x77, 0x34, 0xdc, 0x44,
// //         0x12, 0xf0, 0x0d, 0xd0, 0x8c, 0x92, 0x19, 0xa1, 0xcb, 0x85, 0x07, 0x9b,
// //         0x3e, 0x86, 0x47, 0x36, 0xf6, 0xc6, 0x34, 0x30};

// //     std::vector<uint8_t> calldata{
// //         0x26, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
// //         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
// //         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

// //     TestFixture::execute_and_compare(1'000'000, bytecode, calldata);
// // }

// // TYPED_TEST(VMTraitsTest, MissingRemoveStackOffsetInFallthroughStack)
// // {
// //     std::vector<uint8_t> bytecode{
// //         0x60, 0x80, 0x60, 0x40, 0x52, 0x60, 0x01, 0x5f, 0x55, 0x60, 0x02, 0x60,
// //         0x01, 0x55, 0x34, 0x80, 0x15, 0x60, 0x17, 0x57, 0x5f, 0x80, 0xfd, 0x5b,
// //         0x50, 0x5f, 0x54, 0x5f, 0x54, 0x60, 0x24, 0x91, 0x90, 0x60, 0x76, 0x56,
// //         0x5b, 0x5f, 0x80, 0x00, 0x00, 0x05, 0xf5, 0x54, 0x60, 0x01, 0x54, 0x60,
// //         0x36, 0x91, 0x90, 0x60, 0xa2, 0x56, 0x5b, 0x60, 0x01, 0x81, 0x90, 0x55,
// //         0x50, 0x60, 0xce, 0x56, 0x5b, 0x5f, 0x81, 0x90, 0x50, 0x91, 0x90, 0x50,
// //         0x56, 0x5b, 0x7f, 0x4e, 0x48, 0x7b, 0x71, 0x00, 0x00, 0x00, 0x00, 0x00,
// //         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
// //         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x19, 0x05, 0x55, 0x05,
// //         0x55, 0x55, 0x55, 0x55, 0x55, 0x52, 0x60, 0x24, 0x5f, 0xfd, 0x5b, 0x5f,
// //         0x60, 0x7e, 0x82, 0x60, 0x40, 0x56, 0x5b, 0x91, 0x50, 0x60, 0x87, 0x83,
// //         0x33, 0x33, 0x33, 0x33, 0x34, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
// //         0x44, 0x44, 0x44, 0x44, 0x9c, 0x57, 0x60, 0x9b, 0x60, 0x49, 0x56, 0x5b,
// //         0x5b, 0x92, 0x91, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60};

// //     std::vector<uint8_t> calldata{0xe5, 0xaa, 0x3d, 0x58, 0x00, 0x00, 0x00,
// //                                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
// //                                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
// //                                   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

// //     // TODO: this test is disabled for MONAD_SEVEN onward until evmone has a
// //     // monad revision and can execute with the same gas costs as MONAD_SEVEN
// //     if constexpr (TestFixture::is_monad_trait()) {
// //         if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
// //             return;
// //         }
// //     }

// //     TestFixture::execute_and_compare(1'000'000, bytecode, calldata);
// // }

// // TYPED_TEST(VMTraitsTest, DupStackOverflow)
// // {
// //     auto bytecode = std::vector<std::uint8_t>{};
// //     std::fill_n(std::back_inserter(bytecode), 1024, GAS);
// //     bytecode.push_back(DUP4);

// //     TestFixture::execute(
// //         bytecode, {}, TestFixture::Implementation::Interpreter);

// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
// // }

// // TYPED_TEST(VMTraitsTest, NativeCodeSizeOutOfBound)
// // {
// //     std::vector<uint8_t> bytecode;
// //     CompilerConfig const config{.max_code_size_offset = runtime::bin<1024>};
// //     uint32_t n_jumpi = 20;
// //     for (size_t i = 0; i < n_jumpi; ++i) {
// //         bytecode.push_back(JUMPI);
// //     }
// //     bytecode.push_back(JUMPDEST);
// //     auto icode = make_shared_intercode(bytecode);
// //     auto ncode =
// //         this->vm_.compiler().template compile<typename TestFixture::Trait>(
// //             icode, config);
// //     ASSERT_GT(
// //         ncode->code_size_estimate_before_error(),
// //         *config.max_code_size_offset + n_jumpi * 32);
// //     ASSERT_EQ(ncode->error_code(), Nativecode::ErrorCode::SizeOutOfBound);
// // }

// // TYPED_TEST(VMTraitsTest, MaxDeltaOutOfBound)
// // {
// //     CompilerConfig const config{
// //         .max_code_size_offset = runtime::bin<32 * 1024>};

// //     std::vector<uint8_t> base_bytecode;
// //     for (size_t i = 0; i < 1024; ++i) {
// //         base_bytecode.push_back(PUSH9);
// //         base_bytecode.push_back(1 + static_cast<uint8_t>(i >> 8));
// //         base_bytecode.push_back(static_cast<uint8_t>(i & 255));
// //         for (int j = 0; j < 7; ++j) {
// //             base_bytecode.push_back(0);
// //         }
// //     }
// //     std::vector<uint8_t> bytecode1{base_bytecode};
// //     bytecode1.push_back(JUMPDEST);
// //     auto const icode1 = make_shared_intercode(bytecode1);
// //     auto const ncode1 =
// //         this->vm_.compiler().template compile<typename TestFixture::Trait>(
// //             icode1, config);

// //     TestFixture::pre_execute(10'000, {});
// //     this->result_ = this->vm_.execute_native_entrypoint_raw(
// //         &this->host_.get_interface(),
// //         this->host_.to_context(),
// //         &this->msg_,
// //         icode1,
// //         ncode1->entrypoint());

// //     ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// //     ASSERT_EQ(this->result_.gas_left, 10'000 - (3 * 1024 + 1));

// //     std::vector<uint8_t> bytecode2{base_bytecode};
// //     bytecode2.push_back(PUSH1);
// //     bytecode2.push_back(0x0);
// //     bytecode2.push_back(JUMPDEST);
// //     auto const icode2 = make_shared_intercode(bytecode2);
// //     auto const ncode2 =
// //         this->vm_.compiler().template compile<typename TestFixture::Trait>(
// //             icode2, config);

// //     TestFixture::pre_execute(10'000, {});
// //     this->result_ = this->vm_.execute_native_entrypoint_raw(
// //         &this->host_.get_interface(),
// //         this->host_.to_context(),
// //         &this->msg_,
// //         icode2,
// //         ncode2->entrypoint());

// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);

// //     // Since the basic block in `ncode2` is known to overflow the stack, with
// //     // max_delta > 1024, the native code for the basic block should just jump
// //     // to the error label, without block prologue/epilogue and without the
// //     // pushes to the evm stack inside the basic block.
// //     ASSERT_LT(
// //         *ncode2->code_size_estimate() + 32 * 1024,
// //         *ncode1->code_size_estimate());
// // }

// // TYPED_TEST(VMTraitsTest, MinDeltaOutOfBound)
// // {
// //     CompilerConfig const config{
// //         .max_code_size_offset = runtime::bin<32 * 1024>};

// //     std::vector<uint8_t> base_bytecode;
// //     for (size_t i = 0; i < 1024; ++i) {
// //         base_bytecode.push_back(CODESIZE);
// //     }
// //     base_bytecode.push_back(JUMPDEST);
// //     for (size_t i = 0; i < 1024; ++i) {
// //         base_bytecode.push_back(POP);
// //     }
// //     std::vector<uint8_t> bytecode1{base_bytecode};
// //     bytecode1.push_back(JUMPDEST);
// //     auto const icode1 = make_shared_intercode(bytecode1);
// //     auto const ncode1 =
// //         this->vm_.compiler().template compile<typename TestFixture::Trait>(
// //             icode1, config);

// //     TestFixture::pre_execute(10'000, {});
// //     this->result_ = this->vm_.execute_native_entrypoint_raw(
// //         &this->host_.get_interface(),
// //         this->host_.to_context(),
// //         &this->msg_,
// //         icode1,
// //         ncode1->entrypoint());

// //     ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
// //     ASSERT_EQ(this->result_.gas_left, 10'000 - (2 * 1024 + 1 + 2 * 1024 + 1));

// //     std::vector<uint8_t> bytecode2{base_bytecode};
// //     bytecode2.push_back(POP);
// //     bytecode2.push_back(JUMPDEST);
// //     auto const icode2 = make_shared_intercode(bytecode2);
// //     auto const ncode2 =
// //         this->vm_.compiler().template compile<typename TestFixture::Trait>(
// //             icode2, config);

// //     TestFixture::pre_execute(10'000, {});
// //     this->result_ = this->vm_.execute_native_entrypoint_raw(
// //         &this->host_.get_interface(),
// //         this->host_.to_context(),
// //         &this->msg_,
// //         icode2,
// //         ncode2->entrypoint());

// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);

// //     // We expect native code size of `ncode2` to be smaller, because the last
// //     // basic block has min_delta < -1024, so will just jump to error label,
// //     // without basic block prologue/epilogue.
// //     ASSERT_LT(*ncode2->code_size_estimate(), *ncode1->code_size_estimate());
// // }

// // // Asserts that the compiler and interpreter can have differing behaviour when
// // // running out of gas: the behaviour of the compiler is such that some out of
// // // gas exits can be reported as generic failures, while the interpreter will
// // // always legitimately report an out of gas exit code. Note that in some cases,
// // // the compiler _will_ report an out of gas code (i.e. when gas is deducted by a
// // // runtime component).
// // TYPED_TEST(VMTraitsTest, LoopOutOfGas)
// // {
// //     auto const code = std::vector<uint8_t>{JUMPDEST, PUSH1, 0x0, JUMP};

// //     TestFixture::execute(
// //         30'000, code, {}, TestFixture::Implementation::Interpreter);
// //     ASSERT_EQ(this->result_.status_code, EVMC_OUT_OF_GAS);

// //     TestFixture::execute(
// //         30'000, code, {}, TestFixture::Implementation::Compiler);
// //     ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
// // }

// // TYPED_TEST(VMTraitsTest, ShrCeilOffByOneRegression)
// // {
// //     VM vm{};
// //     evmc_message msg{};
// //     msg.gas = 100;

// //     std::vector<uint8_t> const code(
// //         {0x63, 0x0f, 0xff, 0xff, 0xff, 0x63, 0x0f, 0xff, 0xff, 0xff, 0xfd});
// //     auto const icode = make_shared_intercode(code);
// //     auto const ncode =
// //         vm.compiler().template compile<typename TestFixture::Trait>(icode);
// //     MONAD_VM_ASSERT(ncode->entrypoint() != nullptr);

// //     vm.execute_native_entrypoint_raw(
// //         &this->host_.get_interface(),
// //         this->host_.to_context(),
// //         &msg,
// //         icode,
// //         ncode->entrypoint());
// // }

// // // Compiled directly from the Solidity code in:
// // //   `monad-integration/tests/test_contract_interaction/example.sol`
// // //
// // // The intent of this test is simply to run out of gas when being estimated via
// // // eth_estimateGas, and to validate that the interpreter propagates this status
// // // code. The full integration test based on this contract failed when updating
// // // the client to use the Monad VM before out of gas reporting was re-enabled.
// // TYPED_TEST(VMTraitsTest, EthCallOutOfGas)
// // {
// //     auto const code =
// //         evmc::from_hex(
// //             "0x60806040526004361061007a575f3560e01c8063c3d0f1d01161004d578063c3"
// //             "d0f1d014610110578063c7c41c7514610138578063d0e30db014610160578063e7"
// //             "c9063e1461016a5761007a565b8063209652551461007e57806356cde25b146100"
// //             "a8578063819eb9bb146100e4578063c252ba36146100fa575b5f5ffd5b34801561"
// //             "0089575f5ffd5b50610092610194565b60405161009f91906103c0565b60405180"
// //             "910390f35b3480156100b3575f5ffd5b506100ce60048036038101906100c99190"
// //             "610407565b61019d565b6040516100db91906104fc565b60405180910390f35b34"
// //             "80156100ef575f5ffd5b506100f861024c565b005b348015610105575f5ffd5b50"
// //             "61010e610297565b005b34801561011b575f5ffd5b506101366004803603810190"
// //             "6101319190610407565b6102ec565b005b348015610143575f5ffd5b5061015e60"
// //             "04803603810190610159919061051c565b610321565b005b610168610341565b00"
// //             "5b348015610175575f5ffd5b5061017e61037c565b60405161018b91906103c056"
// //             "5b60405180910390f35b5f600354905090565b60605f83836101ac919061057456"
// //             "5b67ffffffffffffffff8111156101c5576101c46105a7565b5b60405190808252"
// //             "80602002602001820160405280156101f357816020016020820280368337808201"
// //             "91505090505b5090505f8490505b838110156102415760045f8281526020019081"
// //             "526020015f2054828281518110610228576102276105d4565b5b60200260200101"
// //             "818152505080806001019150506101fb565b508091505092915050565b5f61028c"
// //             "576040517f08c379a0000000000000000000000000000000000000000000000000"
// //             "0000000081526004016102839061065b565b60405180910390fd5b61162e600181"
// //             "905550565b5f5f90505b7fffffffffffffffffffffffffffffffffffffffffffff"
// //             "ffffffffffffffffffff8110156102e95760015460045f83815260200190815260"
// //             "20015f2081905550808060010191505061029c565b50565b5f8290505b81811015"
// //             "61031c578060045f8381526020019081526020015f208190555080806001019150"
// //             "506102f1565b505050565b6002548110610336578060028190555061033e565b80"
// //             "6003819055505b50565b7fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c46"
// //             "0751c2402c5c5cc9109c33346040516103729291906106b8565b60405180910390"
// //             "a1565b5f607b6003819055505f60ff90505f613039905080825d815c6040518181"
// //             "52602081602083015e602081f35b5f819050919050565b6103ba816103a8565b82"
// //             "525050565b5f6020820190506103d35f8301846103b1565b92915050565b5f5ffd"
// //             "5b6103e6816103a8565b81146103f0575f5ffd5b50565b5f813590506104018161"
// //             "03dd565b92915050565b5f5f6040838503121561041d5761041c6103d9565b5b5f"
// //             "61042a858286016103f3565b925050602061043b858286016103f3565b91505092"
// //             "50929050565b5f81519050919050565b5f82825260208201905092915050565b5f"
// //             "819050602082019050919050565b610477816103a8565b82525050565b5f610488"
// //             "838361046e565b60208301905092915050565b5f602082019050919050565b5f61"
// //             "04aa82610445565b6104b4818561044f565b93506104bf8361045f565b805f5b83"
// //             "8110156104ef5781516104d6888261047d565b97506104e183610494565b925050"
// //             "6001810190506104c2565b5085935050505092915050565b5f6020820190508181"
// //             "035f83015261051481846104a0565b905092915050565b5f602082840312156105"
// //             "31576105306103d9565b5b5f61053e848285016103f3565b91505092915050565b"
// //             "7f4e487b7100000000000000000000000000000000000000000000000000000000"
// //             "5f52601160045260245ffd5b5f61057e826103a8565b9150610589836103a8565b"
// //             "92508282039050818111156105a1576105a0610547565b5b92915050565b7f4e48"
// //             "7b71000000000000000000000000000000000000000000000000000000005f5260"
// //             "4160045260245ffd5b7f4e487b7100000000000000000000000000000000000000"
// //             "0000000000000000005f52603260045260245ffd5b5f8282526020820190509291"
// //             "5050565b7f6a7573742074657374696e67206572726f72206d6573736167657300"
// //             "000000005f82015250565b5f610645601b83610601565b91506106508261061156"
// //             "5b602082019050919050565b5f6020820190508181035f83015261067281610639"
// //             "565b9050919050565b5f73ffffffffffffffffffffffffffffffffffffffff8216"
// //             "9050919050565b5f6106a282610679565b9050919050565b6106b281610698565b"
// //             "82525050565b5f6040820190506106cb5f8301856106a9565b6106d86020830184"
// //             "6103b1565b939250505056fea26469706673582212202210aaae8cb738bbb3e073"
// //             "496288d456725b3fbcf0489d86bd53a8f79be4091764736f6c634300081e0033")
// //             .value();

// //     auto const data =
// //         evmc::from_hex("0x56cde25b000000000000000000000000000000000000000000000"
// //                        "0000000000000000000000000000000000000000000000000000000"
// //                        "0000000000000000000000004e20")
// //             .value();

// //     TestFixture::execute(
// //         30'000'000, code, data, TestFixture::Implementation::Interpreter);
// //     // code contains PUSH0, so will terminate with a failure pre Shanghai
// //     if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SHANGHAI) {
// //         ASSERT_EQ(this->result_.status_code, EVMC_OUT_OF_GAS);
// //     }
// //     else {
// //         ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
// //     }
// // }

// // namespace
// // {
// //     std::vector<std::variant<evmc_revision, monad_revision>>
// //     monad_evm_revisions()
// //     {
// //         std::vector<std::variant<evmc_revision, monad_revision>> result;
// //         for (auto evm_rev = 0; evm_rev < EVMC_MAX_REVISION; ++evm_rev) {
// //             result.push_back(static_cast<evmc_revision>(evm_rev));
// //         }
// //         for (auto monad_rev = 0; monad_rev <= MONAD_NEXT; ++monad_rev) {
// //             result.push_back(static_cast<monad_revision>(monad_rev));
// //         }
// //         return result;
// //     }

// //     static auto regression_tests =
// //         std::views::cartesian_product(
// //             fs::directory_iterator(monad::test_resource::regression_tests_dir),
// //             monad_evm_revisions()) |
// //         std::ranges::to<std::vector>();

// //     std::string
// //     monad_evm_revision_name(std::variant<evmc_revision, monad_revision> rev)
// //     {
// //         std::string name;
// //         if (std::holds_alternative<monad_revision>(rev)) {
// //             name = monad_revision_to_string(std::get<monad_revision>(rev));
// //         }
// //         else {
// //             name = evmc_revision_to_string(std::get<evmc_revision>(rev));
// //         }
// //         std::replace(name.begin(), name.end(), ' ', '_');
// //         return name;
// //     }

// // }

// // INSTANTIATE_TEST_SUITE_P(
// //     , VMFileTest, ::testing::ValuesIn(regression_tests), ([](auto const &info) {
// //         auto const &[f, rev] = info.param;
// //         return monad_evm_revision_name(rev) + "_" + f.path().stem().string();
// //     }));

// // template <Traits traits>
// // Result<BlockExecOutput> execute(
// //     Block &block, test::db_t &db, vm::VM &vm,
// //     BlockHashBuffer const &block_hash_buffer, bool enable_tracing,
// //     std::vector<Receipt> &receipts,
// //     std::vector<std::vector<CallFrame>> &call_frames)
// // {
// //     InMemoryMachine machine;
// //     mpt::Db db{machine};
// //     db_t tdb{db};
// //     vm::VM vm;

// //     BlockState block_state(db, vm);
// //     BlockMetrics metrics;
// //     EthereumMainnetRev const chain{traits::evm_rev()};
// //     auto const recovered_senders = recover_senders(block.transactions, *pool_);
// //     auto const recovered_authorities =
// //         recover_authorities(block.transactions, *pool_);
// //     std::vector<Address> senders(block.transactions.size());
// //     for (unsigned i = 0; i < recovered_senders.size(); ++i) {
// //         if (recovered_senders[i].has_value()) {
// //             senders[i] = recovered_senders[i].value();
// //         }
// //         else {
// //             return TransactionError::MissingSender;
// //         }
// //     }

// //     std::vector<std::unique_ptr<CallTracerBase>> call_tracers{
// //         block.transactions.size()};
// //     call_frames.resize(block.transactions.size());
// //     std::vector<std::unique_ptr<trace::StateTracer>> state_tracers{
// //         block.transactions.size()};
// //     for (unsigned i = 0; i < block.transactions.size(); ++i) {
// //         call_tracers[i] =
// //             enable_tracing
// //                 ? std::unique_ptr<CallTracerBase>{std::make_unique<CallTracer>(
// //                       block.transactions[i], call_frames[i])}
// //                 : std::unique_ptr<CallTracerBase>{
// //                       std::make_unique<NoopCallTracer>()};
// //         state_tracers[i] = std::unique_ptr<trace::StateTracer>{
// //             std::make_unique<trace::StateTracer>(std::monostate{})};
// //     }

// //     BOOST_OUTCOME_TRY(
// //         receipts,
// //         execute_block<traits>(
// //             chain,
// //             block,
// //             senders,
// //             recovered_authorities,
// //             block_state,
// //             block_hash_buffer,
// //             pool_->fiber_group(),
// //             metrics,
// //             call_tracers,
// //             state_tracers));

// //     block_state.log_debug();
// //     block_state.commit(
// //         bytes32_t{block.header.number},
// //         block.header,
// //         receipts,
// //         std::vector<std::vector<CallFrame>>{block.transactions.size()},
// //         senders,
// //         block.transactions,
// //         block.ommers,
// //         block.withdrawals);
// //     db.finalize(block.header.number, bytes32_t{block.header.number});

// //     BlockExecOutput exec_output;
// //     exec_output.eth_header = db.read_eth_header();
// //     exec_output.eth_block_hash =
// //         to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));

// //     BOOST_OUTCOME_TRY(
// //         validate_output_header(block.header, exec_output.eth_header));

// //     return exec_output;
// // }

// // EXPLICIT_TRAITS(execute);
