// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/namespace_bridge/namespace_bridge_contract.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <memory>
#include <optional>

using namespace monad;
using namespace monad::literals;

namespace
{
    using Trait = MonadTraits<MONAD_NEXT>;
    using PreNextTrait = MonadTraits<MONAD_NINE>;

    constexpr auto SENDER = 0x1234567890123456789012345678901234567890_address;
    constexpr auto OWNER = 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb_address;
    constexpr auto OTHER = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_address;
    constexpr auto NS_ADDR = 0x0000000000000000000000000000000000114eaf_address;
    constexpr uint256_t NETWORK_CHAIN_ID{20143};
    constexpr uint256_t NS_CHAIN_ID =
        (uint256_t{0x11} << 16) | NETWORK_CHAIN_ID;
    constexpr uint64_t NS_ID{0x114eaf};
    constexpr uint32_t REGISTER_NAMESPACE_SELECTOR =
        abi_encode_selector("registerNamespace(uint64,uint256,address)");
    constexpr uint256_t MON{1'000'000'000'000'000'000};

    void write_selector(byte_string &out, uint32_t const selector)
    {
        out.push_back(static_cast<uint8_t>(selector >> 24));
        out.push_back(static_cast<uint8_t>(selector >> 16));
        out.push_back(static_cast<uint8_t>(selector >> 8));
        out.push_back(static_cast<uint8_t>(selector));
    }

    void append_abi_uint256(byte_string &out, uint256_t const &value)
    {
        bytes32_t const be = store_be_as<bytes32_t>(value);
        out.append(be.bytes, be.bytes + sizeof(be.bytes));
    }

    void append_abi_address(byte_string &out, Address const &address)
    {
        out.insert(out.end(), 12, 0);
        out.append(address.bytes, address.bytes + sizeof(address.bytes));
    }

    byte_string registration_calldata(
        uint256_t const &chain_id = NS_CHAIN_ID,
        uint256_t const &mode = static_cast<uint8_t>(NamespaceMode::Native),
        Address const &owner = {})
    {
        byte_string data;
        data.reserve(4 + 3 * 32);
        write_selector(data, REGISTER_NAMESPACE_SELECTOR);
        append_abi_uint256(data, chain_id);
        append_abi_uint256(data, mode);
        append_abi_address(data, owner);
        return data;
    }

    Transaction make_tx(
        uint64_t const nonce, uint256_t const value = 0,
        uint256_t const chain_id = NETWORK_CHAIN_ID)
    {
        return Transaction{
            .sc =
                {.signature =
                     {.r = uint256_t{1}, .s = uint256_t{2}, .y_parity = 0},
                 .chain_id = chain_id},
            .nonce = nonce,
            .max_fee_per_gas = 1,
            .gas_limit = 1'000'000,
            .value = value,
            .to = NAMESPACE_BRIDGE_CA,
            .type = TransactionType::eip1559,
            .max_priority_fee_per_gas = 0,
        };
    }

    class RegistrationHarness
    {
        mpt::Db db_{std::make_unique<MonadInMemoryMachine>()};
        TrieDb tdb_{db_};
        vm::VM vm_{};

    public:
        std::unique_ptr<BlockState> block_state;

        explicit RegistrationHarness(
            std::optional<Account> const &namespace_address_account =
                std::nullopt)
        {
            StateDeltas root_deltas{
                {SENDER,
                 StateDelta{
                     .account = {
                         std::nullopt,
                         Account{.balance = 100 * MON, .nonce = 0}}}}};
            if (namespace_address_account.has_value()) {
                root_deltas.emplace(
                    NS_ADDR,
                    StateDelta{
                        .account = {std::nullopt, *namespace_address_account}});
            }

            auto builder = make_commit_builder(1, tdb_);
            builder->add_state_deltas(root_deltas);
            BlockHeader header{.number = 1};
            bytes32_t const block_id{1};
            tdb_.commit(
                block_id, *builder, header, root_deltas, [&](BlockHeader &h) {
                    h.state_root = tdb_.state_root();
                });
            tdb_.finalize(1, block_id);
            tdb_.set_block_and_prefix(1);
            block_state = std::make_unique<BlockState>(tdb_, vm_);
        }

        Result<Receipt> run(Transaction const &tx)
        {
            BlockMetrics metrics;
            BlockHeader const header{.number = 2};
            BlockHashBufferFinalized const block_hash_buffer;
            boost::fibers::promise<void> previous;
            previous.set_value();
            NoopCallTracer call_tracer;
            trace::StateTracer state_tracer = std::monostate{};
            auto chain_context = ChainContext<Trait>::debug_empty();

            return ExecuteTransaction<Trait>(
                MonadDevnet{},
                0,
                tx,
                SENDER,
                {},
                header,
                block_hash_buffer,
                *block_state,
                metrics,
                previous,
                call_tracer,
                state_tracer,
                chain_context)();
        }

        void commit()
        {
            auto released = std::move(*block_state).release();
            auto builder = make_commit_builder(2, tdb_);
            builder->add_state_deltas(*released.state).add_code(released.code);
            BlockHeader header{.number = 2};
            bytes32_t const block_id{2};
            tdb_.commit(
                block_id,
                *builder,
                header,
                *released.state,
                [&](BlockHeader &h) { h.state_root = tdb_.state_root(); });
            tdb_.finalize(2, block_id);
            block_state = std::make_unique<BlockState>(tdb_, vm_);
        }
    };

    Receipt run_registration(
        RegistrationHarness &harness, byte_string data,
        uint256_t const value = 0,
        uint256_t const tx_chain_id = NETWORK_CHAIN_ID)
    {
        Transaction tx = make_tx(0, value, tx_chain_id);
        tx.data = std::move(data);
        auto result = harness.run(tx);
        EXPECT_FALSE(result.has_error());
        return result.has_value() ? result.value() : Receipt{};
    }
}

TEST(NamespaceBridgeRegistration, ActivatesAtMonadNext)
{
    EXPECT_FALSE(is_precompile<PreNextTrait>(NAMESPACE_BRIDGE_CA));
    EXPECT_TRUE(is_precompile<Trait>(NAMESPACE_BRIDGE_CA));
}

TEST(NamespaceBridgeRegistration, WritesModeOwnerAndInitialCommitment)
{
    RegistrationHarness harness;
    Receipt const receipt =
        run_registration(harness, registration_calldata(NS_CHAIN_ID, 1, OWNER));
    ASSERT_EQ(receipt.status, 1u);

    State state{*harness.block_state, Incarnation{2, 2}};
    ASSERT_TRUE(state.account_exists(NAMESPACE_BRIDGE_CA));
    NamespaceBridgeContract::Variables vars{state};
    EXPECT_EQ(vars.mode(NS_ID).load(), NamespaceMode::Native);
    EXPECT_EQ(vars.owner(NS_ID).load_checked(), OWNER);
    EXPECT_EQ(vars.commitment(NS_ID).load(), NULL_ROOT);
    EXPECT_FALSE(harness.block_state->read_account(NS_ADDR).has_value());

    harness.commit();
    State committed{*harness.block_state, Incarnation{3, 1}};
    ASSERT_TRUE(committed.account_exists(NAMESPACE_BRIDGE_CA));
    NamespaceBridgeContract::Variables committed_vars{committed};
    EXPECT_EQ(committed_vars.mode(NS_ID).load(), NamespaceMode::Native);
    EXPECT_EQ(committed_vars.owner(NS_ID).load_checked(), OWNER);
    EXPECT_EQ(committed_vars.commitment(NS_ID).load(), NULL_ROOT);
}

TEST(NamespaceBridgeRegistration, ZeroOwnerIsPermissionless)
{
    RegistrationHarness harness;
    Receipt const receipt = run_registration(harness, registration_calldata());
    ASSERT_EQ(receipt.status, 1u);

    State state{*harness.block_state, Incarnation{2, 2}};
    ASSERT_TRUE(state.account_exists(NAMESPACE_BRIDGE_CA));
    NamespaceBridgeContract::Variables vars{state};
    EXPECT_EQ(vars.owner(NS_ID).load_checked(), std::nullopt);
}

TEST(NamespaceBridgeRegistration, RejectsDuplicateRegistration)
{
    RegistrationHarness harness;
    ASSERT_EQ(
        run_registration(harness, registration_calldata(NS_CHAIN_ID, 1, OWNER))
            .status,
        1u);

    Transaction tx = make_tx(1);
    tx.data = registration_calldata(NS_CHAIN_ID, 1, OTHER);
    auto const second = harness.run(tx);
    ASSERT_FALSE(second.has_error());
    EXPECT_EQ(second.value().status, 0u);

    State state{*harness.block_state, Incarnation{2, 3}};
    ASSERT_TRUE(state.account_exists(NAMESPACE_BRIDGE_CA));
    NamespaceBridgeContract::Variables vars{state};
    EXPECT_EQ(vars.owner(NS_ID).load_checked(), OWNER);
}

TEST(NamespaceBridgeRegistration, RejectsMalformedArguments)
{
    RegistrationHarness harness;
    byte_string data = registration_calldata();
    data.resize(data.size() - 32);
    EXPECT_EQ(run_registration(harness, std::move(data)).status, 0u);
}

TEST(NamespaceBridgeRegistration, RejectsUnsupportedMode)
{
    RegistrationHarness harness;
    EXPECT_EQ(
        run_registration(harness, registration_calldata(NS_CHAIN_ID, 2)).status,
        0u);
}

TEST(NamespaceBridgeRegistration, RejectsGlobalChainId)
{
    RegistrationHarness harness;
    EXPECT_EQ(
        run_registration(harness, registration_calldata(NETWORK_CHAIN_ID))
            .status,
        0u);
}

TEST(NamespaceBridgeRegistration, RejectsNonZeroValue)
{
    RegistrationHarness harness;
    EXPECT_EQ(run_registration(harness, registration_calldata(), 1).status, 0u);
}

TEST(NamespaceBridgeRegistration, DoesNotOverwriteRootAddress)
{
    RegistrationHarness harness{Account{.balance = 42, .nonce = 7}};
    ASSERT_EQ(run_registration(harness, registration_calldata()).status, 1u);

    auto const account = harness.block_state->read_account(NS_ADDR);
    ASSERT_TRUE(account.has_value());
    EXPECT_EQ(account->balance, uint256_t{42});
    EXPECT_EQ(account->nonce, 7u);
}
