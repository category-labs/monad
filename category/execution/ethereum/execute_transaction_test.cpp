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
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <memory>
#include <optional>

using namespace monad;

using db_t = TrieDb;

TYPED_TEST(TraitsTest, irrevocable_gas_and_refund_new_contract)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    static constexpr auto initial_balance = 56'000'000'000'000'000;
    static constexpr auto actual_gas_cost = [] {
        if constexpr (TestFixture::Trait::evm_rev() == EVMC_FRONTIER) {
            return 21'000;
        }
        else {
            return 53'000;
        }
    }();
    static constexpr auto gas_limit = actual_gas_cost + 2'000;
    static constexpr auto max_fee_per_gas = 10;

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, initial_balance);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction const tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .nonce = 25,
        .max_fee_per_gas = max_fee_per_gas,
        .gas_limit = gas_limit,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer;

    boost::fibers::promise<void> prev{};
    prev.set_value();

    NoopCallTracer noop_call_tracer;
    trace::StateTracer noop_state_tracer = std::monostate{};

    auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
        EthereumMainnet{},
        0,
        tx,
        from,
        {},
        header,
        block_hash_buffer,
        bs,
        metrics,
        prev,
        noop_call_tracer,
        noop_state_tracer)();

    ASSERT_TRUE(!receipt.has_error());

    EXPECT_EQ(receipt.value().status, 1u);
    {
        State state{bs, Incarnation{0, 0}};
        uint256_t const final_balance_uint256 = state.get_balance(from);
        ASSERT_TRUE(
            final_balance_uint256 < std::numeric_limits<uint64_t>::max());
        auto const final_balance = static_cast<uint64_t>(final_balance_uint256);
        if constexpr (TestFixture::is_monad_trait()) {
            if constexpr (TestFixture::Trait::monad_rev() == MONAD_ZERO) {
                EXPECT_EQ(
                    final_balance,

                    initial_balance - actual_gas_cost * max_fee_per_gas);
            }
            else {
                EXPECT_EQ(
                    final_balance,
                    initial_balance - gas_limit * max_fee_per_gas);
            }
        }
        else {
            EXPECT_EQ(
                final_balance,
                initial_balance - actual_gas_cost * max_fee_per_gas);
        }

        EXPECT_EQ(state.get_nonce(from), 26); // EVMC will inc for creation
    }
    // check if miner gets the right reward
    if constexpr (TestFixture::is_monad_trait()) {
        if constexpr (TestFixture::Trait::monad_rev() == MONAD_ZERO) {
            EXPECT_EQ(receipt.value().gas_used, actual_gas_cost);
        }
        else {
            EXPECT_EQ(receipt.value().gas_used, gas_limit);
        }
    }
    else {
        EXPECT_EQ(receipt.value().gas_used, actual_gas_cost);
    }
}

TYPED_TEST(TraitsTest, TopLevelCreate)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    {
        constexpr uint256_t WEI_PER_MON{1000000000000000000};
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 20 * WEI_PER_MON);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    auto const data = byte_string(154'776, '\x60');

    Transaction const tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .nonce = 25,
        .max_fee_per_gas = 100'000'000'000,
        .gas_limit = 68'491'176,
        .value = 0,
        .to = std::nullopt,
        .data = data,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer;

    NoopCallTracer noop_call_tracer;
    trace::StateTracer noop_state_tracer = std::monostate{};

    boost::fibers::promise<void> prev{};
    prev.set_value();

    auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
        MonadTestnet{},
        0,
        tx,
        from,
        {},
        header,
        block_hash_buffer,
        bs,
        metrics,
        prev,
        noop_call_tracer,
        noop_state_tracer)();

    if constexpr (TestFixture::is_monad_trait()) {
        if constexpr (TestFixture::Trait::monad_rev() >= MONAD_TWO) {
            ASSERT_TRUE(receipt.has_value());
        }
        else {
            ASSERT_TRUE(receipt.has_error());
        }
    }
    else {
        if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SHANGHAI) {
            ASSERT_TRUE(receipt.has_error());
        }
        else {
            ASSERT_TRUE(receipt.has_value());
        }
    }
}

TYPED_TEST(TraitsTest, refunds_delete)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    static constexpr auto initial_balance = 56'000'000'000'000'000;
    static constexpr auto max_fee_per_gas = 100'000'000'000;
    static constexpr auto gas_limit_tx1 = 200'000;
    static constexpr auto gas_limit_tx2 = 50'000;

    static constexpr auto gas_charged_tx1 = [] {
        if constexpr (TestFixture::is_monad_trait()) {
            if constexpr (TestFixture::Trait::monad_rev() > MONAD_ZERO) {
                // Since MONAD_ONE full gas_limit is charged
                return gas_limit_tx1;
            }
        }

        if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
            return 41'092;
        }
        else if constexpr (TestFixture::Trait::evm_rev() == EVMC_ISTANBUL) {
            // Gas decreased due to calldata cost reduction in EIP-2028
            // where gas per non-zero byte was reduced from 68 to 16
            return 41'040;
        }
        else {
            // Gas increased due to storage repricing in Berlin
            return 43'140;
        }
    }();

    static constexpr auto gas_charged_tx2 = [] {
        if constexpr (TestFixture::is_monad_trait()) {
            if constexpr (TestFixture::Trait::monad_rev() > MONAD_ZERO) {
                // Since MONAD_ONE full gas_limit is charged
                return gas_limit_tx2;
            }
        }
        return 26'025;
    }();

    // X -> X -> 0
    static constexpr auto storage_refund_tx2_evm_uncapped = [] {
        if constexpr (TestFixture::Trait::evm_rev() >= EVMC_LONDON) {
            return 4'800;
        }
        else {
            return 15'000;
        }
    }();
    static constexpr auto storage_refund_tx2 = [=] {
        if constexpr (TestFixture::is_monad_trait()) {
            if constexpr (TestFixture::Trait::monad_rev() > MONAD_ZERO) {
                return 0;
            }
        }
        if constexpr (TestFixture::Trait::evm_rev() >= EVMC_LONDON) {
            // due to EIP-3529 introduced in London revision
            return std::min(
                gas_charged_tx2 / 5, storage_refund_tx2_evm_uncapped);
        }
        else {
            return std::min(
                gas_charged_tx2 / 2, storage_refund_tx2_evm_uncapped);
        }
    }();

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    // Sets s[0] = 1 if passed any data, clears s[0] if data is empty.
    auto const contract_code =
        evmc::from_hex("0x3615600b576001600055005b6000600055").value();

    {
        State state{bs, Incarnation{0, 0}};

        state.add_to_balance(from, initial_balance);
        state.set_nonce(from, 25);

        state.create_contract(contract);
        state.set_code(contract, contract_code);

        bs.merge(state);
    }

    // 0 -> 0 -> Z
    {
        Transaction const set_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 25,
            .max_fee_per_gas = max_fee_per_gas,
            .gas_limit = gas_limit_tx1,
            .to = contract,
            .data = evmc::from_hex("0x01").value(),
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            set_tx,
            from,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();

        ASSERT_TRUE(receipt.has_value());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            auto const final_balance_uint256 = state.get_balance(from);
            ASSERT_TRUE(
                final_balance_uint256 < std::numeric_limits<uint64_t>::max());
            auto const final_balance =
                static_cast<uint64_t>(final_balance_uint256);

            EXPECT_EQ(
                final_balance,
                initial_balance - (gas_charged_tx1 * max_fee_per_gas));
        }
    }

    // X -> X -> 0
    {
        Transaction const zero_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 26,
            .max_fee_per_gas = max_fee_per_gas,
            .gas_limit = gas_limit_tx2,
            .to = contract,
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            zero_tx,
            from,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            auto const final_balance_uint256 = state.get_balance(from);
            ASSERT_TRUE(
                final_balance_uint256 < std::numeric_limits<uint64_t>::max());
            auto const final_balance =
                static_cast<uint64_t>(final_balance_uint256);

            EXPECT_EQ(
                final_balance,
                initial_balance -
                    ((gas_charged_tx1 + gas_charged_tx2) * max_fee_per_gas) +
                    (storage_refund_tx2 * max_fee_per_gas));
        }
    }
}

TYPED_TEST(TraitsTest, refunds_delete_then_set)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    static constexpr auto initial_balance = 56'000'000'000'000'000;
    static constexpr auto max_fee_per_gas = 100'000'000'000;

    static constexpr auto slot = bytes32_t{};
    auto const initial_value = intx::be::store<bytes32_t>(uint256_t{1});

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    // s[0] = 0; s[0] = 1
    auto const contract_code = evmc::from_hex("0x60006000556001600055").value();

    {
        State state{bs, Incarnation{0, 0}};

        state.add_to_balance(from, initial_balance);
        state.set_nonce(from, 25);

        state.create_contract(contract);
        state.set_code(contract, contract_code);
        state.set_storage(contract, slot, initial_value);

        bs.merge(state);
    }

    // X -> X -> 0 then X -> 0 -> X
    {
        static constexpr auto gas_limit_tx =
            50'000; // should be high ehough to cover actual gas used + low gas
                    // SSTORE stipend for all revisions

        Transaction const set_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 25,
            .max_fee_per_gas = max_fee_per_gas,
            .gas_limit = gas_limit_tx,
            .to = contract,
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            set_tx,
            from,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            auto const final_balance_uint256 = state.get_balance(from);
            ASSERT_TRUE(
                final_balance_uint256 < std::numeric_limits<uint64_t>::max());
            auto const final_balance =
                static_cast<uint64_t>(final_balance_uint256);

            static constexpr auto gas_charged = [] {
                if constexpr (TestFixture::is_monad_trait()) {
                    if constexpr (
                        TestFixture::Trait::monad_rev() > MONAD_ZERO) {
                        // Since MONAD_ONE full gas_limit is charged
                        return gas_limit_tx;
                    }
                }

                if constexpr (
                    TestFixture::Trait::evm_rev() == EVMC_CONSTANTINOPLE) {
                    return 26'212;
                }

                if constexpr (TestFixture::Trait::evm_rev() == EVMC_ISTANBUL) {
                    return 26'812;
                }

                if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
                    return 46'012;
                }
                else {
                    return 26'112;
                }
            }();

            static constexpr auto storage_refund_evm_uncapped = [] {
                if constexpr (
                    TestFixture::Trait::evm_rev() == EVMC_CONSTANTINOPLE) {
                    return 4800;
                }
                if constexpr (TestFixture::Trait::evm_rev() == EVMC_ISTANBUL) {
                    return 4200;
                }
                if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
                    return 15000;
                }
                else {
                    return 2800;
                }
            }();
            static constexpr auto storage_refund = [=] {
                if constexpr (TestFixture::is_monad_trait()) {
                    if constexpr (
                        TestFixture::Trait::monad_rev() > MONAD_ZERO) {
                        return 0;
                    }
                }
                if constexpr (TestFixture::Trait::evm_rev() >= EVMC_LONDON) {
                    // due to EIP-3529 introduced in London revision
                    return std::min(
                        gas_charged / 5, storage_refund_evm_uncapped);
                }
                else {
                    return std::min(
                        gas_charged / 2, storage_refund_evm_uncapped);
                    ;
                }
            }();

            EXPECT_EQ(
                final_balance,
                initial_balance - (gas_charged * max_fee_per_gas) +
                    (storage_refund * max_fee_per_gas));
        }
    }
}

/**
 * This test reproduces a bug whereby EIP-7702 authorizations with malleated s
 * components could be used to crash execution via differing checks in reserve
 * balance and authorization processing.
 *
 * At a high level, the issue was:
 *   - Malleated s-component signatures were rejected by the authorization
 *     processing code (i.e. a tuple with a high s-component would not be
 *     applied).
 *   - However, because `recover_authority` permitted such signatures, the
 *     reserve balance code would process that tuple as if the authorization had
 *     in fact been applied.
 *   - This led to an invariant violation when performing reserve balance checks
 *     (undelegated account treated as delegated).
 *
 *  The code in this test reproduces an on-chain version of the issue by hand.
 */
TYPED_TEST(MonadTraitsTest, malleated_s_authorization)
{
    using intx::operator""_u256;

    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        GTEST_SKIP()
            << "Test skipped: not applicable before EVM Prague revision";
    }

    static constexpr auto from{
        0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266_address};
    static constexpr auto auth_target{
        0x1111111111111111111111111111111111111111_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    static constexpr uint256_t wei_per_mon = 1'000'000'000'000'000'000;

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 10'000 * wei_per_mon);
        bs.merge(state);
    }

    {
        AuthorizationEntry const auth_entry{
            .sc =
                {
                    .r =
                        0x1eab7e601bdfbacb2201a7b190033ef7a70e4c41250be98d2c34e925aea4000f_u256,
                    .s =
                        0x93e2654638633c57e3e590838941cb0a45b2e1c5d9fd24cb886afb7219969e57_u256,
                    .chain_id = 20143,
                    .y_parity = 0,
                },
            .address = auth_target,
            .nonce = 0,
        };
        EXPECT_TRUE(auth_entry.sc.has_upper_s());

        Transaction const high_s_tx{
            .sc =
                {
                    .r =
                        0x1cfae88075cbd6d065ca2d8ce49bb67e882eb730ddce3760e61eaeb8d0d8bc07_u256,
                    .s =
                        0x2e322c15cfa818f804366fa30fcb926271de3696b56632d3620ebf8f6953c01_u256,
                    .chain_id = 20143,
                    .y_parity = 0,
                },
            .nonce = 0,
            .max_fee_per_gas = 1'767'666'666'666,
            .gas_limit = 6'000'000,
            .value = 0,
            .to = std::nullopt,
            .type = TransactionType::eip7702,
            .data = {},
            .access_list = {},
            .max_priority_fee_per_gas = 1'767'666'666'666,
            .max_fee_per_blob_gas = {},
            .blob_versioned_hashes = {},
            .authorization_list = {auth_entry},
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const senders = std::vector<Address>{from};
        auto const authorities =
            std::vector<std::vector<std::optional<Address>>>{
                {recover_authority(auth_entry)}};
        auto const senders_and_authorities =
            ankerl::unordered_dense::segmented_set<Address>{{from}};

        // `recover_authority` should return nullopt due to high s-value
        EXPECT_FALSE(authorities[0][0].has_value());

        MonadChainContext chain_context{
            .grandparent_senders_and_authorities = nullptr,
            .parent_senders_and_authorities = nullptr,
            .senders_and_authorities = senders_and_authorities,
            .senders = senders,
            .authorities = authorities,
        };

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            high_s_tx,
            from,
            authorities[0],
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer,
            [&header, &chain_context](
                Address const &sender,
                Transaction const &tx,
                uint64_t const i,
                State &state) {
                return revert_monad_transaction<typename TestFixture::Trait>(
                    sender,
                    tx,
                    header.base_fee_per_gas.value_or(0),
                    i,
                    state,
                    chain_context);
            })();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);
    }
}
