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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/execute_domain_block.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::domain;
using namespace monad::test;

namespace
{
    using traits = MonadTraits<MONAD_TEN>;

    constexpr uint64_t DOMAIN = 0x114eaf;
    constexpr uint64_t NUMBER = 5;
    constexpr uint64_t TIMESTAMP = 1'000;
    Address const SENDER{0x5e};
    Address const COUNTER{0xc0};
    Address const ENV{0xe0};

    // Increments slot 1.
    byte_string const COUNTER_CODE{
        0x60, 0x01, 0x54, 0x60, 0x01, 0x01, 0x60, 0x01, 0x55, 0x00};
    // Returns COUNTER_CODE.
    byte_string const COUNTER_INITCODE =
        byte_string{
            0x60,
            0x0a,
            0x60,
            0x0c,
            0x60,
            0x00,
            0x39,
            0x60,
            0x0a,
            0x60,
            0x00,
            0xf3} +
        COUNTER_CODE;
    // Stores CHAINID, NUMBER, COINBASE, BASEFEE, BLOCKHASH(NUMBER - 1) and
    // TIMESTAMP in slots 0 to 5.
    byte_string const ENV_CODE{0x46, 0x60, 0x00, 0x55, 0x43, 0x60, 0x01, 0x55,
                               0x41, 0x60, 0x02, 0x55, 0x48, 0x60, 0x03, 0x55,
                               0x60, 0x01, 0x43, 0x03, 0x40, 0x60, 0x04, 0x55,
                               0x42, 0x60, 0x05, 0x55, 0x00};

    struct TestL1Chain final : MonadChain
    {
        uint256_t get_chain_id() const override
        {
            return DOMAIN & NETWORK_CHAIN_ID_MASK;
        }

        monad_revision get_monad_revision(uint64_t) const override
        {
            return traits::monad_rev();
        }

        GenesisState get_genesis_state() const override
        {
            return GenesisState{};
        }
    };

    Transaction transaction(
        uint64_t const nonce, std::optional<Address> const to,
        byte_string data = {}, uint256_t const value = 0)
    {
        return Transaction{
            .sc = {.signature = {.r = 1, .s = 1}, .chain_id = DOMAIN},
            .nonce = nonce,
            .max_fee_per_gas = DOMAIN_GAS_PRICE,
            .gas_limit = 200'000,
            .value = value,
            .to = to,
            .data = std::move(data)};
    }

    struct ExecuteDomainBlockTest : public ::testing::Test
    {
        mpt::Db db{std::make_unique<MonadInMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm;
        fiber::PriorityPool pool{1, 1};
        TestL1Chain l1_chain;
        BlockHashBufferFinalized block_hashes;

        ExecuteDomainBlockTest()
        {
            auto const account = [](byte_string const &code) {
                return StateDelta{
                    .account = {
                        std::nullopt,
                        Account{.code_hash = to_bytes(keccak256(code))}}};
            };
            commit_simple(
                tdb,
                StateDeltas{
                    {COUNTER, account(COUNTER_CODE)}, {ENV, account(ENV_CODE)}},
                Code{
                    {to_bytes(keccak256(COUNTER_CODE)),
                     vm::make_shared_intercode(COUNTER_CODE)},
                    {to_bytes(keccak256(ENV_CODE)),
                     vm::make_shared_intercode(ENV_CODE)}},
                bytes32_t{1},
                BlockHeader{.number = 0});
            for (uint64_t n = 0; n < NUMBER; ++n) {
                block_hashes.set(n, bytes32_t{0x100 + n});
            }
        }

        // Executes a domain block with these transactions against the
        // committed state, returning its receipts and leaving its state in
        // `block_state`.
        std::vector<Receipt> execute(
            BlockState &block_state, std::vector<Transaction> transactions,
            std::vector<Address> senders)
        {
            DerivedDomainBlock const derived{
                .number = NUMBER,
                .timestamp = TIMESTAMP,
                .prev_randao = bytes32_t{7},
                .transactions = std::move(transactions),
                .senders = std::move(senders)};
            auto receipts = execute_domain_block<traits>(
                DomainChain{l1_chain, DOMAIN},
                derived,
                execution_header<traits>(derived),
                block_state,
                block_hashes,
                pool);
            EXPECT_TRUE(receipts.has_value());
            return std::move(receipts).value();
        }
    };

    bytes32_t
    read_storage(State &state, Address const &address, bytes32_t const &key)
    {
        // State reads storage only of an account it has loaded.
        EXPECT_TRUE(state.account_exists(address));
        return state.get_storage(address, key);
    }

    std::vector<uint64_t> statuses(std::vector<Receipt> const &receipts)
    {
        std::vector<uint64_t> result;
        for (auto const &receipt : receipts) {
            result.push_back(receipt.status);
        }
        return result;
    }
}

TEST_F(ExecuteDomainBlockTest, transactions_pay_no_gas)
{
    BlockState block_state{tdb, vm};
    auto const receipts = execute(
        block_state,
        {transaction(0, COUNTER),
         // A second transaction from the same sender in the block.
         transaction(1, COUNTER),
         // Bad nonce: skipped.
         transaction(1, COUNTER),
         // Carries value: skipped.
         transaction(2, COUNTER, {}, 1),
         transaction(2, std::nullopt, COUNTER_INITCODE)},
        std::vector(5, SENDER));

    EXPECT_EQ(statuses(receipts), (std::vector<uint64_t>{1, 1, 0, 0, 1}));
    // gas_used is cumulative, and a skipped transaction uses none.
    EXPECT_GT(receipts[0].gas_used, 0);
    EXPECT_GT(receipts[1].gas_used, receipts[0].gas_used);
    EXPECT_EQ(receipts[2].gas_used, receipts[1].gas_used);
    EXPECT_EQ(receipts[3].gas_used, receipts[1].gas_used);
    EXPECT_GT(receipts[4].gas_used, receipts[1].gas_used);

    State state{block_state, Incarnation{NUMBER + 1, 0}};
    EXPECT_EQ(state.get_nonce(SENDER), 3);
    EXPECT_EQ(state.get_balance(SENDER), 0);
    EXPECT_FALSE(state.account_exists(Address{}));
    EXPECT_EQ(read_storage(state, COUNTER, bytes32_t{1}), bytes32_t{2});
    auto const created = create_contract_address(SENDER, 2);
    EXPECT_EQ(state.get_code_hash(created), to_bytes(keccak256(COUNTER_CODE)));
}

TEST_F(ExecuteDomainBlockTest, deliveries_keep_the_relayer_nonce)
{
    BlockState block_state{tdb, vm};
    auto const delivery = [](uint64_t const message_nonce) {
        return make_domain_system_transaction(
            DOMAIN,
            COUNTER,
            DOMAIN_GAS_PRICE,
            100'000,
            DOMAIN & NETWORK_CHAIN_ID_MASK,
            Address{0xf0},
            Address{0xf1},
            byte_string{0x01, 0x02},
            message_nonce);
    };
    auto const receipts = execute(
        block_state,
        {transaction(0, COUNTER), delivery(7), delivery(8)},
        {SENDER, DOMAIN_SYSTEM_RELAYER, DOMAIN_SYSTEM_RELAYER});

    EXPECT_EQ(statuses(receipts), (std::vector<uint64_t>{1, 1, 1}));
    State state{block_state, Incarnation{NUMBER + 1, 0}};
    EXPECT_EQ(read_storage(state, COUNTER, bytes32_t{1}), bytes32_t{3});
    EXPECT_FALSE(state.account_exists(DOMAIN_SYSTEM_RELAYER));
}

TEST_F(ExecuteDomainBlockTest, block_environment_is_the_domain_block)
{
    BlockState block_state{tdb, vm};
    auto const receipts = execute(block_state, {transaction(0, ENV)}, {SENDER});
    ASSERT_EQ(statuses(receipts), std::vector<uint64_t>{1});

    State state{block_state, Incarnation{NUMBER + 1, 0}};
    auto const slot = [&](uint64_t const n) {
        return read_storage(state, ENV, bytes32_t{n});
    };
    EXPECT_EQ(slot(0), bytes32_t{DOMAIN});
    EXPECT_EQ(slot(1), bytes32_t{NUMBER});
    EXPECT_EQ(slot(2), bytes32_t{});
    EXPECT_EQ(slot(3), bytes32_t{static_cast<uint64_t>(DOMAIN_GAS_PRICE)});
    EXPECT_EQ(slot(4), bytes32_t{0x100 + NUMBER - 1});
    EXPECT_EQ(slot(5), bytes32_t{TIMESTAMP});
}

TEST_F(ExecuteDomainBlockTest, monad_precompiles_are_off)
{
    BlockState block_state{tdb, vm};
    // On the L1 these calls reach the staking and reserve balance contracts
    // and revert on the unknown selector; on a domain the addresses are
    // empty accounts.
    auto const receipts = execute(
        block_state,
        {transaction(0, staking::STAKING_CA, {0xde, 0xad, 0xbe, 0xef}),
         transaction(1, RESERVE_BALANCE_CA, {0xde, 0xad, 0xbe, 0xef})},
        {SENDER, SENDER});
    EXPECT_EQ(statuses(receipts), (std::vector<uint64_t>{1, 1}));
}

TEST(ExecutionHeader, follows_the_derived_block_and_the_revision)
{
    DerivedDomainBlock const block{
        .number = NUMBER,
        .l1_block_number = 100,
        .timestamp = TIMESTAMP,
        .prev_randao = bytes32_t{7},
        .slot_number = 3};

    // Cancun's fields.
    auto const header = execution_header<MonadTraits<MONAD_ZERO>>(block);
    EXPECT_EQ(header.number, NUMBER);
    EXPECT_EQ(header.timestamp, TIMESTAMP);
    EXPECT_EQ(header.prev_randao, bytes32_t{7});
    EXPECT_EQ(header.gas_limit, DOMAIN_BLOCK_GAS_LIMIT);
    EXPECT_EQ(header.base_fee_per_gas, DOMAIN_GAS_PRICE);
    EXPECT_EQ(header.beneficiary, Address{});
    EXPECT_EQ(header.withdrawals_root, NULL_ROOT);
    EXPECT_EQ(header.blob_gas_used, 0);
    EXPECT_EQ(header.excess_blob_gas, 0);
    EXPECT_EQ(header.parent_beacon_block_root, bytes32_t{});
    EXPECT_EQ(header.requests_hash, std::nullopt);
    EXPECT_EQ(header.block_access_list_hash, std::nullopt);
    EXPECT_EQ(header.slot_number, std::nullopt);

    // Amsterdam's.
    auto const next = execution_header<MonadTraits<MONAD_NEXT>>(block);
    EXPECT_EQ(next.requests_hash, compute_requests_hash({}));
    EXPECT_EQ(next.block_access_list_hash, bytes32_t{});
    EXPECT_EQ(next.slot_number, 3);
}
