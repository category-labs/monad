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
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/execute_domain_block.hpp>
#include <category/execution/domain/spoke.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

using namespace monad;
using namespace monad::domain;
using namespace monad::test;

namespace
{
    using traits = MonadTraits<MONAD_TEN>;

    constexpr uint64_t DOMAIN = 0x114eaf;
    constexpr uint64_t NUMBER = 5;
    Address const HUB{0xab};
    // The account the policy admits, and one it does not.
    Address const MEMBER{0x5e};
    Address const STRANGER{0x5f};
    // Contracts with the counter's code: one without a policy, one whose
    // policy admits MEMBER, and one whose policy makes a call.
    Address const OPEN{0xc0};
    Address const GUARDED{0xc1};
    Address const BADLY_GUARDED{0xc2};
    Address const POLICY{0xa0};
    Address const CALLING_POLICY{0xa1};
    Address const FORWARDER{0xf0};
    Address const GAUGE{0xf1};

    // Increments slot 1.
    byte_string const COUNTER_CODE{
        0x60, 0x01, 0x54, 0x60, 0x01, 0x01, 0x60, 0x01, 0x55, 0x00};
    // canCall returns whether the caller is the account in slot 0.
    byte_string const POLICY_CODE{
        0x60, 0x04, 0x35, 0x5f, 0x54, 0x14, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3};
    // canCall calls the identity precompile and returns true.
    byte_string const CALLING_POLICY_CODE{
        0x5f,
        0x5f,
        0x5f,
        0x5f,
        0x60,
        0x04,
        0x5a,
        0xfa,
        0x50,
        0x60,
        0x01,
        0x5f,
        0x52,
        0x60,
        0x20,
        0x5f,
        0xf3};
    // Calls the address in its calldata with all its gas, ignores the outcome
    // and stores 7 in slot 2.
    byte_string const FORWARDER_CODE{
        0x5f,
        0x5f,
        0x5f,
        0x5f,
        0x5f,
        0x5f,
        0x35,
        0x5a,
        0xf1,
        0x50,
        0x60,
        0x07,
        0x60,
        0x02,
        0x55,
        0x00};

    // Stores the gas it starts with in slot 0.
    byte_string const GAUGE_CODE{0x5a, 0x5f, 0x55, 0x00};

    // Initcode that calls `target` with all its gas, ignores the outcome and
    // deploys no code.
    byte_string calling_initcode(Address const &target)
    {
        return byte_string{0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73} +
               byte_string{target.bytes, sizeof(target.bytes)} +
               byte_string{0x5a, 0xf1, 0x00};
    }

    byte_string word(Address const &address)
    {
        byte_string result(32, 0);
        std::copy_n(address.bytes, sizeof(address.bytes), result.data() + 12);
        return result;
    }

    // The slot of DomainSpoke's accessPolicies[target]: the mapping is the
    // contract's fourth storage variable.
    bytes32_t access_policy_slot(Address const &target)
    {
        byte_string encoded = word(target);
        encoded.resize(64, 0);
        encoded[63] = 3;
        return to_bytes(keccak256(encoded));
    }

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
        std::optional<Address> const to, byte_string data = {},
        uint64_t const gas_limit = 300'000)
    {
        return Transaction{
            .sc = {.signature = {.r = 1, .s = 1}, .chain_id = DOMAIN},
            .nonce = 0,
            .max_fee_per_gas = DOMAIN_GAS_PRICE,
            .gas_limit = gas_limit,
            .to = to,
            .data = std::move(data)};
    }

    struct DomainAccessCheckTest : public ::testing::Test
    {
        mpt::Db db{std::make_unique<MonadInMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm;
        fiber::PriorityPool pool{1, 1};
        TestL1Chain l1_chain;
        BlockHashBufferFinalized block_hashes;
        BlockState block_state{tdb, vm};

        DomainAccessCheckTest()
        {
            StateDeltas accounts;
            Code code;
            auto const add = [&](Address const &address,
                                 byte_string const &bytes) {
                auto const hash = to_bytes(keccak256(bytes));
                accounts.emplace(
                    address,
                    StateDelta{
                        .account = {std::nullopt, Account{.code_hash = hash}}});
                code.emplace(hash, vm::make_shared_intercode(bytes));
            };
            add(DOMAIN_SPOKE,
                domain_spoke_code(DOMAIN, DOMAIN & NETWORK_CHAIN_ID_MASK, HUB));
            add(OPEN, COUNTER_CODE);
            add(GUARDED, COUNTER_CODE);
            add(BADLY_GUARDED, COUNTER_CODE);
            add(POLICY, POLICY_CODE);
            add(CALLING_POLICY, CALLING_POLICY_CODE);
            add(FORWARDER, FORWARDER_CODE);
            add(GAUGE, GAUGE_CODE);
            commit_simple(
                tdb, accounts, code, bytes32_t{1}, BlockHeader{.number = 0});
            for (uint64_t n = 0; n < NUMBER; ++n) {
                block_hashes.set(n, bytes32_t{0x100 + n});
            }

            // The spoke names the policies, and POLICY admits MEMBER.
            State state{block_state, Incarnation{NUMBER, 0}};
            auto const set = [&](Address const &address,
                                 bytes32_t const &key,
                                 Address const &value) {
                EXPECT_TRUE(state.account_exists(address));
                state.set_storage(address, key, to_bytes(word(value)));
            };
            set(DOMAIN_SPOKE, access_policy_slot(GUARDED), POLICY);
            set(DOMAIN_SPOKE,
                access_policy_slot(BADLY_GUARDED),
                CALLING_POLICY);
            set(POLICY, bytes32_t{}, MEMBER);
            EXPECT_TRUE(block_state.can_merge(state));
            block_state.merge(state);
        }

        // Executes a domain block of one transaction from `sender`, checking
        // its call frames against the spoke iff `checked`, and returns the
        // transaction's receipt.
        Receipt execute(
            Address const &sender, Transaction const &tx,
            bool const checked = true)
        {
            DerivedDomainBlock const derived{
                .number = NUMBER,
                .timestamp = 1'000,
                .prev_randao = bytes32_t{7},
                .transactions = {tx},
                .senders = {sender}};
            auto header = domain_execution_inputs<traits>(
                derived, block_hashes.get(NUMBER - 1));
            DomainChain const chain{l1_chain, DOMAIN};

            auto const authorities =
                recover_authorities(derived.transactions, pool);
            auto const senders_and_authorities =
                combine_senders_and_authorities(derived.senders, authorities);
            auto chain_ctx = domain_chain_context<traits>(
                senders_and_authorities, derived.senders, authorities);
            chain_ctx.domain_spoke =
                checked ? std::optional{DOMAIN_SPOKE} : std::nullopt;
            std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
            call_tracers.push_back(std::make_unique<NoopCallTracer>());
            std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
            state_tracers.push_back(
                std::make_unique<trace::StateTracer>(std::monostate{}));
            BlockMetrics block_metrics;
            auto receipts = execute_block_transactions<traits>(
                chain,
                header,
                derived.transactions,
                derived.senders,
                authorities,
                block_state,
                block_hashes,
                pool.fiber_group(),
                block_metrics,
                call_tracers,
                state_tracers,
                chain_ctx,
                nullptr,
                false);
            EXPECT_TRUE(receipts.has_value());
            EXPECT_EQ(receipts.value().size(), 1);
            return std::move(receipts.value()[0]);
        }

        bytes32_t storage(Address const &address, uint64_t const slot)
        {
            State state{block_state, Incarnation{NUMBER + 1, 0}};
            // State reads storage only of an account it has loaded.
            EXPECT_TRUE(state.account_exists(address));
            return state.get_storage(address, bytes32_t{slot});
        }
    };
}

TEST_F(DomainAccessCheckTest, contract_without_a_policy_admits_everyone)
{
    auto const receipt = execute(STRANGER, transaction(OPEN));

    EXPECT_EQ(receipt.status, 1);
    EXPECT_EQ(storage(OPEN, 1), bytes32_t{1});
}

TEST_F(DomainAccessCheckTest, frame_pays_for_its_check)
{
    auto const gas = [this] {
        return static_cast<uint64_t>(
            load_be<uint256_t>(storage(GAUGE, 0).bytes));
    };

    EXPECT_EQ(execute(STRANGER, transaction(GAUGE), false).status, 1);
    auto const unchecked = gas();
    EXPECT_EQ(execute(MEMBER, transaction(GAUGE)).status, 1);
    auto const checked = gas();

    EXPECT_LT(checked, unchecked);
    // The check may use at most 50,000 gas.
    EXPECT_GE(checked + 50'000, unchecked);
}

TEST_F(DomainAccessCheckTest, policy_admits_whom_it_names)
{
    auto const receipt = execute(MEMBER, transaction(GUARDED));

    EXPECT_EQ(receipt.status, 1);
    EXPECT_EQ(storage(GUARDED, 1), bytes32_t{1});
}

TEST_F(DomainAccessCheckTest, policy_denies_everyone_else)
{
    auto const receipt = execute(STRANGER, transaction(GUARDED));

    EXPECT_EQ(receipt.status, 0);
    EXPECT_EQ(storage(GUARDED, 1), bytes32_t{});
}

TEST_F(DomainAccessCheckTest, no_frame_is_checked_without_the_spoke)
{
    auto const receipt = execute(STRANGER, transaction(GUARDED), false);

    EXPECT_EQ(receipt.status, 1);
    EXPECT_EQ(storage(GUARDED, 1), bytes32_t{1});
}

TEST_F(DomainAccessCheckTest, inner_frames_are_checked)
{
    auto const receipt = execute(STRANGER, transaction(FORWARDER, word(OPEN)));

    EXPECT_EQ(receipt.status, 1);
    EXPECT_EQ(storage(OPEN, 1), bytes32_t{1});
    EXPECT_EQ(storage(FORWARDER, 2), bytes32_t{7});
}

// The forwarder ignores that its call failed, and the transaction reverts all
// the same.
TEST_F(DomainAccessCheckTest, denied_frame_reverts_the_transaction)
{
    // The policy sees the forwarder as the caller, which it does not admit.
    auto const receipt = execute(MEMBER, transaction(FORWARDER, word(GUARDED)));

    EXPECT_EQ(receipt.status, 0);
    EXPECT_EQ(storage(GUARDED, 1), bytes32_t{});
    EXPECT_EQ(storage(FORWARDER, 2), bytes32_t{});
}

TEST_F(DomainAccessCheckTest, denied_frame_reverts_a_creation)
{
    auto const admitted =
        execute(STRANGER, transaction(std::nullopt, calling_initcode(OPEN)));
    auto const denied =
        execute(MEMBER, transaction(std::nullopt, calling_initcode(GUARDED)));

    EXPECT_EQ(admitted.status, 1);
    EXPECT_EQ(storage(OPEN, 1), bytes32_t{1});
    EXPECT_EQ(denied.status, 0);
    EXPECT_EQ(storage(GUARDED, 1), bytes32_t{});
}

TEST_F(DomainAccessCheckTest, policy_may_call_nothing)
{
    auto const receipt = execute(MEMBER, transaction(BADLY_GUARDED));

    EXPECT_EQ(receipt.status, 0);
    EXPECT_EQ(storage(BADLY_GUARDED, 1), bytes32_t{});
}

TEST_F(DomainAccessCheckTest, frame_without_gas_for_its_check_is_denied)
{
    // 21,000 of the gas limit is intrinsic: under 50,000 is left.
    auto const receipt = execute(STRANGER, transaction(OPEN, {}, 70'000));

    EXPECT_EQ(receipt.status, 0);
    EXPECT_EQ(storage(OPEN, 1), bytes32_t{});
}
