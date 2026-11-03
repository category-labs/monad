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
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/access_status.h>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/evm-as/sugar.hpp>
#include <category/vm/utils/evm-as/validator.hpp>
#include <category/vm/vm.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <cstring>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace monad;

namespace
{
    using GuestTraits = EvmTraits<MONAD_ETH_PRAGUE>;
    constexpr auto address = 0x00000000000000000000000000000000deadbeef_address;
    constexpr auto slot =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto value =
        0x000000000000000000000000000000000000000000000000000000000000abcd_bytes32;

    static_assert(!std::is_polymorphic_v<PartialTrieDb>);
    static_assert(!std::is_polymorphic_v<CallTracerBase>);
    static_assert(std::is_same_v<trace::StateTracer, std::monostate>);

    byte_string empty_blob()
    {
        return {'M', 'Z', 'W', 1, 0, 0, 0, 0};
    }

    void set_root(byte_string &blob, size_t offset)
    {
        auto const wire = static_cast<uint32_t>(offset);
        std::memcpy(blob.data() + 4, &wire, sizeof(wire));
    }

    byte_string unresolved_blob()
    {
        auto blob = empty_blob();
        set_root(blob, blob.size());
        mpt::append_digest(blob, value);
        return blob;
    }

    byte_string history_blob(bool unresolved_storage)
    {
        auto blob = empty_blob();
        auto const storage = mpt::NodeId{blob.size()};
        if (unresolved_storage) {
            mpt::append_digest(blob, value);
        }
        else {
            auto const key = keccak256(slot.bytes);
            mpt::append_storage(blob, mpt::NibblesView{key}, value);
        }
        set_root(blob, blob.size());
        auto const key = keccak256(BLOCK_HISTORY_ADDRESS.bytes);
        mpt::append_acct(
            blob,
            storage,
            Account{.code_hash = BLOCK_HISTORY_CODE_HASH},
            mpt::NibblesView{key});
        return blob;
    }

    struct Fixture
    {
        byte_string blob;
        PartialTrieDb db;
        vm::VM vm;
        BlockState block{db, vm};
        State state{block, Incarnation{1, 1}};

        explicit Fixture(byte_string bytes, CodeIndex codes = {})
            : blob{std::move(bytes)}
            , db{mpt::OffsetTrie{blob}, std::move(codes)}
        {
        }

        std::optional<Account> read_account(Address const &a)
        {
            bool resolved;
            auto const account = block.read_account(a, resolved);
            EXPECT_TRUE(resolved);
            return account;
        }
    };

    Result<Receipt> execute_transaction(
        Fixture &f, Transaction const &tx, uint64_t index = 0,
        Address const &beneficiary = {})
    {
        EthereumMainnet const chain;
        BlockHeader const header{.number = 1, .beneficiary = beneficiary};
        BlockHashBufferFinalized const hashes;
        BlockMetrics metrics{};
        NoopCallTracer call_tracer{};
        trace::StateTracer state_tracer{};
        ChainContext<GuestTraits> const chain_ctx{};
        boost::fibers::promise<void> promise{};
        auto prev = promise.get_future();
        promise.set_value();
        return ExecuteTransaction<GuestTraits>{
            chain,
            index,
            tx,
            address,
            {},
            header,
            hashes,
            f.block,
            metrics,
            prev,
            call_tracer,
            state_tracer,
            chain_ctx,
            nullptr}();
    }

    Transaction transfer(uint64_t nonce)
    {
        return Transaction{
            .sc = {.signature = {.r = 1, .s = 1}},
            .nonce = nonce,
            .max_fee_per_gas = 1,
            .gas_limit = 21'000,
            .value = 7,
            .to = BLOCK_HISTORY_ADDRESS};
    }
}

TEST(GuestState, UnresolvedAccessCachesOnlyMetadata)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{unresolved_blob()};
    EXPECT_FALSE(f.db.try_read_account(address));
    bool resolved = true;
    EXPECT_FALSE(f.block.read_account(address, resolved));
    EXPECT_FALSE(resolved);
    f.state.push();
    for (int i = 0; i < 2; ++i) {
        auto const expected = i == 0 ? MONAD_ACCESS_COLD : MONAD_ACCESS_WARM;
        EXPECT_EQ(f.state.access_account(address), expected);
        EXPECT_EQ(f.state.access_storage<GuestTraits>(address, slot), expected);
    }
    ASSERT_EQ(f.state.current().size(), 1);
    EXPECT_FALSE(f.state.current().at(address).recent().is_resolved());
    ASSERT_EQ(f.state.original().size(), 1);
    EXPECT_FALSE(f.state.original().at(address).is_resolved());
    EXPECT_TRUE(f.state.current_frame_dirty_accounts().contains(address));
    f.state.pop_reject();
    EXPECT_TRUE(f.state.current().empty());
    EXPECT_FALSE(f.state.original().at(address).is_resolved());
    EXPECT_DEATH(
        (void)f.state.get_nonce(address), testing::HasSubstr("is_resolved"));
    EXPECT_TRUE(std::move(f.block).release().state->empty());
}

TEST(GuestState, UnresolvedPlaceholdersRejectAccountDataAccess)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{unresolved_blob()};
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_COLD);
    EXPECT_DEATH(
        (void)f.state.account_exists(address),
        testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        (void)f.state.get_balance(address), testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        (void)f.state.get_original_balance(address),
        testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        (void)f.state.get_nonce(address), testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        (void)f.state.get_code(address), testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        (void)f.state.get_storage(address, slot),
        testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        f.state.set_nonce(address, 1), testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        f.state.add_to_balance(address, 1), testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        f.state.create_contract(address), testing::HasSubstr("is_resolved"));
    EXPECT_DEATH(
        (void)f.state.original().at(address).has_account(),
        testing::HasSubstr("is_resolved"));
    // Access-only placeholders must not turn into proven absence at merge.
    f.block.merge(f.state);
    EXPECT_TRUE(std::move(f.block).release().state->empty());
}

TEST(GuestState, UnresolvedAccessPreservesExistingCacheEntries)
{
    auto const unresolved_key = keccak256(address.bytes);
    auto const cached_key = keccak256(BLOCK_HISTORY_ADDRESS.bytes);
    ASSERT_NE(unresolved_key.bytes[0] >> 4, cached_key.bytes[0] >> 4);
    auto blob = empty_blob();
    std::array<mpt::NodeId, 16> children{};
    children[unresolved_key.bytes[0] >> 4] = mpt::NodeId{blob.size()};
    mpt::append_digest(blob, value);
    children[cached_key.bytes[0] >> 4] = mpt::NodeId{blob.size()};
    mpt::append_acct(
        blob,
        mpt::NULL_ID,
        Account{.nonce = 7},
        mpt::NibblesView{cached_key}.substr(1));
    set_root(blob, blob.size());
    mpt::append_branch(blob, children);
    Fixture f{std::move(blob)};
    auto const *cached = &f.state.original_account_state(BLOCK_HISTORY_ADDRESS);
    for (int i = 0; i < 2; ++i) {
        auto const expected = i == 0 ? MONAD_ACCESS_COLD : MONAD_ACCESS_WARM;
        EXPECT_EQ(f.state.access_account(address), expected);
        EXPECT_EQ(f.state.access_storage<GuestTraits>(address, slot), expected);
        ASSERT_EQ(f.state.original().size(), 2);
        EXPECT_FALSE(f.state.original().at(address).is_resolved());
        ASSERT_EQ(&f.state.original().at(BLOCK_HISTORY_ADDRESS), cached);
        EXPECT_EQ(cached->get_nonce(), 7);
    }
    ASSERT_EQ(f.state.current().size(), 1);
    EXPECT_FALSE(f.state.current().at(address).recent().is_resolved());
    f.block.merge(f.state);
    auto const deltas = std::move(f.block).release();
    ASSERT_EQ(deltas.state->size(), 1);
    EXPECT_TRUE(deltas.state->contains(BLOCK_HISTORY_ADDRESS));
}

TEST(GuestState, UnresolvedWarmthFollowsFrameRollback)
{
    Fixture f{unresolved_blob()};
    auto const other = BLOCK_HISTORY_ADDRESS;
    auto const other_slot = value;

    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_COLD);
    f.state.push();
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_WARM);
    EXPECT_EQ(f.state.access_account(other), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_COLD);
    f.state.push();
    EXPECT_EQ(f.state.access_account(other), MONAD_ACCESS_WARM);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, other_slot),
        MONAD_ACCESS_COLD);
    f.state.pop_accept();
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, other_slot),
        MONAD_ACCESS_WARM);
    f.state.pop_reject();

    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_WARM);
    EXPECT_EQ(f.state.access_account(other), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, other_slot),
        MONAD_ACCESS_COLD);
    f.state.push();
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(other, slot), MONAD_ACCESS_COLD);
    f.state.pop_accept();
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(other, slot), MONAD_ACCESS_WARM);

    EXPECT_FALSE(f.state.original().at(address).is_resolved());
    EXPECT_FALSE(f.state.current().at(address).recent().is_resolved());
    f.block.merge(f.state);
    State next{f.block, Incarnation{1, 2}};
    EXPECT_EQ(next.access_account(address), MONAD_ACCESS_COLD);
    EXPECT_EQ(next.access_storage<GuestTraits>(other, slot), MONAD_ACCESS_COLD);
}

TEST(GuestState, PrewarmedCallCannotHideBehindOutOfGas)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    using namespace monad::vm::utils;
    auto const target = 0x0000000000000000000000000000000000c0ffee_address;
    // Write storage, then CALL with enough gas for a warm access but not a
    // cold one. Charging cold would revert the write instead of rejecting
    // a witness that omits the account needed by the call.
    auto eb = evm_as::EvmBuilder<GuestTraits>{};
    eb.sstore(0, 1).call(evm_as::sugar::CallArgs{.address = target}).stop();
    ASSERT_TRUE(evm_as::validate(eb));
    std::vector<uint8_t> code;
    evm_as::compile(eb, code);
    auto const code_hash =
        to_bytes(keccak256(byte_string_view{code.data(), code.size()}));
    auto const target_key = keccak256(target.bytes);
    auto const target_path = mpt::NibblesView{target_key}.substr(1);
    auto leaf = empty_blob();
    set_root(leaf, leaf.size());
    mpt::append_acct(leaf, mpt::NULL_ID, Account{.nonce = 1}, target_path);
    auto const target_hash = mpt::OffsetTrie{leaf}.state_root();

    auto const make_blob = [&](bool const hide_target) {
        auto blob = empty_blob();
        std::array<mpt::NodeId, 16> children{};
        for (auto const &[a, account] : std::array{
                 std::pair{address, Account{.balance = 1'000'000}},
                 std::pair{
                     BLOCK_HISTORY_ADDRESS,
                     Account{.code_hash = code_hash, .nonce = 1}}}) {
            auto const key = keccak256(a.bytes);
            children[key.bytes[0] >> 4] = mpt::NodeId{blob.size()};
            mpt::append_acct(
                blob, mpt::NULL_ID, account, mpt::NibblesView{key}.substr(1));
        }
        MONAD_ASSERT(children[target_key.bytes[0] >> 4] == mpt::NULL_ID);
        children[target_key.bytes[0] >> 4] = mpt::NodeId{blob.size()};
        if (hide_target) {
            mpt::append_digest(blob, target_hash);
        }
        else {
            mpt::append_acct(
                blob, mpt::NULL_ID, Account{.nonce = 1}, target_path);
        }
        set_root(blob, blob.size());
        mpt::append_branch(blob, children);
        return blob;
    };
    for (bool const coinbase : {false, true}) {
        SCOPED_TRACE(coinbase ? "coinbase" : "access list");
        Fixture full{
            make_blob(false), {{code_hash, vm::make_shared_intercode(code)}}};
        Fixture hidden{
            make_blob(true), {{code_hash, vm::make_shared_intercode(code)}}};
        EXPECT_EQ(full.db.state_root(), hidden.db.state_root());
        auto tx = transfer(0);
        tx.value = 0;
        tx.type = TransactionType::eip2930;
        tx.gas_limit = 43'600;
        if (!coinbase) {
            tx.access_list = {{target, {}}};
            tx.gas_limit += 2'400;
        }
        auto const &beneficiary = coinbase ? target : address;
        auto const result = execute_transaction(full, tx, 0, beneficiary);
        ASSERT_TRUE(result.has_value());
        ASSERT_EQ(result.value().status, 1);
        State after{full.block, Incarnation{1, 2}};
        EXPECT_EQ(after.get_nonce(BLOCK_HISTORY_ADDRESS), 1);
        EXPECT_EQ(after.get_storage(BLOCK_HISTORY_ADDRESS, {}), bytes32_t{1});
        // Backtraces can contain NULs, which truncate a regex match.
        EXPECT_DEATH(
            (void)execute_transaction(hidden, tx, 0, beneficiary),
            testing::HasSubstr("is_resolved"));
    }
}

TEST(GuestState, ProvenAbsenceIsCachedAndCanBeCreated)
{
    Fixture f{empty_blob()};
    auto const result = f.db.try_read_account(address);
    ASSERT_TRUE(result.has_value());
    EXPECT_FALSE(result->has_value());
    bool resolved = false;
    auto account = f.block.read_account(address, resolved);
    ASSERT_TRUE(resolved);
    EXPECT_FALSE(account);
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_COLD);
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_WARM);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_WARM);
    EXPECT_FALSE(f.state.account_exists(address));
    f.state.set_nonce(address, 1);
    f.state.set_storage(address, slot, value);
    f.block.merge(f.state);
    resolved = false;
    account = f.block.read_account(address, resolved);
    ASSERT_TRUE(resolved);
    ASSERT_TRUE(account);
    EXPECT_EQ(account->nonce, 1);

    State next{f.block, Incarnation{1, 2}};
    EXPECT_EQ(next.get_nonce(address), 1);
    EXPECT_EQ(next.access_account(address), MONAD_ACCESS_COLD);
    EXPECT_EQ(next.get_storage(address, slot), value);
}

TEST(GuestState, WarmthAndWritesFollowFrameRollback)
{
    Fixture f{empty_blob()};
    f.state.push();
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_COLD);
    f.state.pop_reject();
    EXPECT_TRUE(f.state.current().empty());
    EXPECT_EQ(f.state.original().size(), 1);
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_COLD);
    f.state.push();
    f.state.set_nonce(address, 7);
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_WARM);
    f.state.pop_reject();
    EXPECT_FALSE(f.state.account_exists(address));
    EXPECT_EQ(f.state.access_account(address), MONAD_ACCESS_WARM);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(address, slot), MONAD_ACCESS_WARM);
}

TEST(GuestState, MissingHistoryAccountFallsBackWithoutCachingAbsence)
{
    Fixture f{unresolved_blob()};
    EXPECT_EQ(get_block_hash_history(f.state, 1), bytes32_t{});
    ASSERT_EQ(f.state.original().size(), 1);
    EXPECT_FALSE(f.state.original().at(BLOCK_HISTORY_ADDRESS).is_resolved());
    EXPECT_TRUE(f.state.current().empty());
    EXPECT_TRUE(std::move(f.block).release().state->empty());
}

TEST(GuestState, MissingStorageCanBeWarmedButCannotBeRead)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{history_blob(true)};
    EXPECT_EQ(f.state.access_account(BLOCK_HISTORY_ADDRESS), MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(BLOCK_HISTORY_ADDRESS, slot),
        MONAD_ACCESS_COLD);
    EXPECT_EQ(
        f.state.access_storage<GuestTraits>(BLOCK_HISTORY_ADDRESS, slot),
        MONAD_ACCESS_WARM);
    EXPECT_EQ(get_block_hash_history(f.state, 1), bytes32_t{});
    EXPECT_TRUE(f.state.original().at(BLOCK_HISTORY_ADDRESS).storage_.empty());
    EXPECT_DEATH(
        (void)f.state.get_storage(BLOCK_HISTORY_ADDRESS, slot),
        testing::HasSubstr("value.has_value()"));
    auto const deltas = std::move(f.block).release();
    EXPECT_TRUE(deltas.state->at(BLOCK_HISTORY_ADDRESS).storage.empty());
}

TEST(GuestState, HistoryReadsCurrentAndBlockCachesAndRollsBack)
{
    Fixture f{history_blob(false)};
    EXPECT_EQ(get_block_hash_history(f.state, 1), value);
    f.state.push();
    f.state.set_storage(BLOCK_HISTORY_ADDRESS, slot, bytes32_t{});
    EXPECT_EQ(get_block_hash_history(f.state, 1), bytes32_t{});
    f.state.pop_reject();
    EXPECT_EQ(get_block_hash_history(f.state, 1), value);
    f.state.push();
    f.state.set_storage(BLOCK_HISTORY_ADDRESS, slot, BLOCK_HISTORY_CODE_HASH);
    f.state.pop_accept();
    EXPECT_EQ(get_block_hash_history(f.state, 1), BLOCK_HISTORY_CODE_HASH);
    f.block.merge(f.state);
    State next{f.block, Incarnation{1, 2}};
    EXPECT_EQ(get_block_hash_history(next, 1), BLOCK_HISTORY_CODE_HASH);
}

TEST(GuestState, SequentialExecutionRejectsBadNonceWithoutMerging)
{
    Fixture f{empty_blob()};
    auto absent = execute_transaction(f, transfer(1));
    ASSERT_TRUE(absent.has_error());
    EXPECT_EQ(absent.error(), TransactionError::BadNonce);
    EXPECT_FALSE(f.read_account(address));

    f.state.set_nonce(address, 7);
    f.state.add_to_balance(address, 1'000'000);
    f.block.merge(f.state);
    auto const before = f.read_account(address);
    for (uint64_t const nonce : {6u, 8u}) {
        auto result = execute_transaction(f, transfer(nonce));
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), TransactionError::BadNonce);
        EXPECT_EQ(f.read_account(address), before);
        EXPECT_FALSE(f.read_account(BLOCK_HISTORY_ADDRESS));
    }
}

TEST(GuestState, SequentialTransactionsReadPreviousMerge)
{
    Fixture f{empty_blob()};
    f.state.set_nonce(address, 7);
    f.state.add_to_balance(address, 1'000'000);
    f.block.merge(f.state);
    for (uint64_t i = 0; i < 2; ++i) {
        auto result = execute_transaction(f, transfer(7 + i), i);
        ASSERT_TRUE(result.has_value());
        EXPECT_EQ(result.value().status, 1);
        auto const sender = f.read_account(address);
        ASSERT_TRUE(sender);
        EXPECT_EQ(sender->nonce, 8 + i);
        auto const recipient = f.read_account(BLOCK_HISTORY_ADDRESS);
        ASSERT_TRUE(recipient);
        EXPECT_EQ(recipient->balance, 7 * (i + 1));
    }
    auto const before = f.read_account(address);
    auto tx = transfer(9);
    tx.value = 1'000'000;
    auto result = execute_transaction(f, tx, 2);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), TransactionError::InsufficientBalance);
    EXPECT_EQ(f.read_account(address), before);
}
