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

// The guest State over witness blobs: what a row answers for an address or
// slot the witness proves present, proves absent, or cannot prove at all.
// Blobs are built with the production node writers, as in
// test_partial_trie_db.cpp.

#include <zkvm/state/account_state.hpp>
#include <zkvm/state/key_hash.hpp>
#include <zkvm/state/slot_map.hpp>
#include <zkvm/state/state.hpp>
#include <zkvm/state/test_witness.hpp>

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/vm.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::zkvm::test;

// ---------------------------------------------------------------------------
// Account reads
// ---------------------------------------------------------------------------

TEST(ZkvmState, AbsentAccountReadsAsEmpty)
{
    Fixture f{empty_blob()};
    auto &s = f.state;
    EXPECT_FALSE(s.account_exists(ADDR));
    EXPECT_TRUE(s.account_is_dead(ADDR));
    EXPECT_FALSE(s.account_has_code_or_nonce(ADDR));
    EXPECT_EQ(s.get_nonce(ADDR), 0);
    EXPECT_EQ(s.get_balance(ADDR), 0);
    EXPECT_EQ(s.get_code_hash(ADDR), NULL_HASH);
    EXPECT_EQ(s.get_code_size(ADDR), 0);
    EXPECT_EQ(s.get_code(ADDR)->intercode()->size(), 0);
    EXPECT_FALSE(s.is_current_incarnation(ADDR));
    EXPECT_FALSE(s.is_touched(ADDR));
    EXPECT_FALSE(s.is_destructed(ADDR));
    EXPECT_EQ(s.get_storage(ADDR, SLOT_1), bytes32_t{});
    EXPECT_EQ(s.get_transient_storage(ADDR, SLOT_1), bytes32_t{});
}

TEST(ZkvmState, PresentAccountDecodesLeaf)
{
    Account const acct{.balance = 1234, .code_hash = CODE_HASH, .nonce = 7};
    Fixture f{account_blob(ADDR, acct), codes({{CODE_HASH, varcode(CODE)}})};
    auto &s = f.state;
    EXPECT_TRUE(s.account_exists(ADDR));
    EXPECT_FALSE(s.account_is_dead(ADDR));
    EXPECT_TRUE(s.account_has_code_or_nonce(ADDR));
    EXPECT_EQ(s.get_nonce(ADDR), 7);
    EXPECT_EQ(s.get_balance(ADDR), 1234);
    EXPECT_EQ(s.get_code_hash(ADDR), CODE_HASH);
    EXPECT_EQ(s.get_code_size(ADDR), CODE.size());
    EXPECT_EQ(s.get_code(ADDR)->intercode()->size(), CODE.size());
    std::array<uint8_t, 8> buffer{};
    EXPECT_EQ(s.copy_code(ADDR, 1, buffer.data(), buffer.size()), 4);
    EXPECT_EQ(buffer[0], 0x00);
    EXPECT_EQ(buffer[3], 0xf3);
    // A witness account carries the {0, 0} stamp, never the block's.
    EXPECT_FALSE(s.is_current_incarnation(ADDR));
    EXPECT_FALSE(s.is_touched(ADDR));
    EXPECT_FALSE(s.is_destructed(ADDR));

    // A different address under the same single-leaf root is proven absent.
    EXPECT_FALSE(s.account_exists(OTHER));
    EXPECT_EQ(s.get_nonce(OTHER), 0);
}

TEST(ZkvmState, TwoPresentAccountsDecodeSeparately)
{
    Fixture f{two_account_blob(
        ADDR, Account{.nonce = 1}, OTHER, Account{.nonce = 2})};
    auto &s = f.state;
    EXPECT_EQ(s.get_nonce(ADDR), 1);
    EXPECT_EQ(s.get_nonce(OTHER), 2);
    EXPECT_EQ(s.get_nonce(ADDR), 1);
    EXPECT_FALSE(
        s.account_exists(0x0000000000000000000000000000000000000001_address));
}

TEST(ZkvmState, PresentAccountBesideHiddenSubtree)
{
    Fixture f{branch_blob(OTHER, Account{.nonce = 3}, ADDR)};
    auto &s = f.state;
    EXPECT_EQ(s.get_nonce(OTHER), 3);
    EXPECT_EQ(s.get_balance(OTHER), 0);
    EXPECT_TRUE(s.account_exists(OTHER));
}

TEST(ZkvmStateDeathTest, UnprovenAccountReadsAbort)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{hidden_blob()};
    auto &s = f.state;
    auto const unproven = testing::HasSubstr("account not in the witness");
    EXPECT_DEATH((void)s.account_exists(ADDR), unproven);
    EXPECT_DEATH((void)s.account_is_dead(ADDR), unproven);
    EXPECT_DEATH((void)s.get_nonce(ADDR), unproven);
    EXPECT_DEATH((void)s.get_balance(ADDR), unproven);
    EXPECT_DEATH((void)s.get_code_hash(ADDR), unproven);
    EXPECT_DEATH((void)s.get_code(ADDR), unproven);
    EXPECT_DEATH((void)s.get_code_size(ADDR), unproven);
    EXPECT_DEATH((void)s.is_current_incarnation(ADDR), unproven);
    EXPECT_DEATH((void)s.get_storage(ADDR, SLOT_1), unproven);
    // The row exists without the account; what is not witness data still
    // answers.
    EXPECT_FALSE(s.is_touched(ADDR));
    EXPECT_FALSE(s.is_destructed(ADDR));
    EXPECT_EQ(s.get_transient_storage(ADDR, SLOT_1), bytes32_t{});
}

TEST(ZkvmStateDeathTest, UnprovenAccountBesidePresentLeaf)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{branch_blob(OTHER, Account{.nonce = 3}, ADDR)};
    auto &s = f.state;
    EXPECT_EQ(s.get_nonce(OTHER), 3);
    EXPECT_DEATH(
        (void)s.get_nonce(ADDR),
        testing::HasSubstr("account not in the witness"));
    EXPECT_EQ(s.get_nonce(OTHER), 3);
}

// ---------------------------------------------------------------------------
// Storage reads
// ---------------------------------------------------------------------------

TEST(ZkvmState, StorageReadsWitnessValue)
{
    Fixture f{storage_blob(ADDR, Account{.nonce = 1}, SLOT_1, VAL_1)};
    auto &s = f.state;
    EXPECT_EQ(s.get_storage(ADDR, SLOT_1), VAL_1);
    EXPECT_EQ(s.get_storage(ADDR, SLOT_1), VAL_1);
    // The single leaf spells SLOT_1's hash, which proves SLOT_2 absent.
    EXPECT_EQ(s.get_storage(ADDR, SLOT_2), bytes32_t{});
    EXPECT_EQ(s.get_storage(ADDR, SLOT_1), VAL_1);
}

TEST(ZkvmState, StorageOfAccountWithoutStorageIsZero)
{
    Fixture f{account_blob(ADDR, Account{.nonce = 1})};
    EXPECT_EQ(f.state.get_storage(ADDR, SLOT_1), bytes32_t{});
    EXPECT_EQ(f.state.get_storage(ADDR, SLOT_2), bytes32_t{});
}

TEST(ZkvmState, ManySlotsReadConsistently)
{
    Fixture f{storage_blob(ADDR, Account{.nonce = 1}, SLOT_1, VAL_1)};
    auto &s = f.state;
    // Well past SLOT_INDEX_FROM, so the reads go through the index.
    for (uint64_t i = 0; i < 4 * zkvm::SLOT_INDEX_FROM; ++i) {
        bytes32_t const key{i};
        EXPECT_EQ(s.get_storage(ADDR, key), i == 1 ? VAL_1 : bytes32_t{});
    }
    for (uint64_t i = 0; i < 4 * zkvm::SLOT_INDEX_FROM; ++i) {
        bytes32_t const key{i};
        EXPECT_EQ(s.get_storage(ADDR, key), i == 1 ? VAL_1 : bytes32_t{});
    }
}

TEST(ZkvmState, TryGetStorageAnswersOnlyWhatTheWitnessProves)
{
    Fixture f{hidden_storage_blob(ADDR, Account{.nonce = 1})};
    auto &s = f.state;
    // The storage subtree is withheld: no answer, and no abort.
    EXPECT_EQ(s.try_get_storage(ADDR, SLOT_1), std::nullopt);
    // An absent account reads as zero, proven.
    EXPECT_EQ(s.try_get_storage(OTHER, SLOT_1), bytes32_t{});
    Fixture g{storage_blob(ADDR, Account{.nonce = 1}, SLOT_1, VAL_1)};
    EXPECT_EQ(g.state.try_get_storage(ADDR, SLOT_1), VAL_1);
    EXPECT_EQ(g.state.try_get_storage(ADDR, SLOT_2), bytes32_t{});
}

TEST(ZkvmStateDeathTest, UnprovenStorageAbortsOnRead)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{hidden_storage_blob(ADDR, Account{.nonce = 1})};
    auto &s = f.state;
    // The account itself is proven.
    EXPECT_EQ(s.get_nonce(ADDR), 1);
    EXPECT_TRUE(s.account_exists(ADDR));
    EXPECT_DEATH(
        (void)s.get_storage(ADDR, SLOT_1),
        testing::HasSubstr("storage slot not in the witness"));
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

TEST(ZkvmState, CodeTableServesWitnessCode)
{
    Fixture f{empty_blob(), codes({{CODE_HASH, varcode(CODE)}})};
    auto &s = f.state;
    EXPECT_EQ(s.read_code(NULL_HASH)->intercode()->size(), 0);
    EXPECT_EQ(s.read_code(CODE_HASH)->intercode()->size(), CODE.size());
    EXPECT_EQ(s.read_code(CODE_HASH), s.read_code(CODE_HASH));
}

TEST(ZkvmStateDeathTest, MissingCodeAborts)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{account_blob(ADDR, Account{.code_hash = CODE_HASH})};
    auto &s = f.state;
    EXPECT_EQ(s.get_code_hash(ADDR), CODE_HASH);
    auto const missing = testing::HasSubstr("code not in the witness");
    EXPECT_DEATH((void)s.read_code(CODE_HASH), missing);
    EXPECT_DEATH((void)s.get_code(ADDR), missing);
    EXPECT_DEATH((void)s.get_code_size(ADDR), missing);
}

TEST(ZkvmState, CodeAccessorsServeTheRow)
{
    Fixture f{
        account_blob(ADDR, Account{.code_hash = CODE_HASH}),
        codes({{CODE_HASH, varcode(CODE)}})};
    auto &s = f.state;
    EXPECT_EQ(s.get_code_size(ADDR), CODE.size());
    EXPECT_EQ(s.get_code(ADDR), s.read_code(CODE_HASH));
    std::array<uint8_t, 8> buf{};
    EXPECT_EQ(s.copy_code(ADDR, 1, buf.data(), buf.size()), CODE.size() - 1);
    EXPECT_TRUE(std::equal(CODE.begin() + 1, CODE.end(), buf.begin()));
    // An absent account has no code and no row cache to consult.
    EXPECT_EQ(s.get_code_size(OTHER), 0);
    EXPECT_EQ(s.copy_code(OTHER, 0, buf.data(), buf.size()), 0);
    EXPECT_EQ(s.get_code(OTHER), s.read_code(NULL_HASH));
}

TEST(ZkvmState, CodeCacheFollowsTheCodeHash)
{
    // The row resolves its code once per distinct hash: a set_code, and a
    // rollback that restores the earlier hash, each re-resolve.
    Fixture f{
        account_blob(ADDR, Account{.nonce = 1}),
        codes({{CODE_HASH, varcode(CODE)}})};
    auto &s = f.state;
    EXPECT_EQ(s.get_code_size(ADDR), 0);
    s.set_code(ADDR, byte_string_view{CODE.data(), CODE.size()});
    EXPECT_EQ(s.get_code_size(ADDR), CODE.size());
    std::vector<uint8_t> const longer{0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf3};
    s.push();
    s.set_code(ADDR, byte_string_view{longer.data(), longer.size()});
    EXPECT_EQ(s.get_code_size(ADDR), longer.size());
    s.pop_reject();
    EXPECT_EQ(s.get_code_size(ADDR), CODE.size());
    EXPECT_EQ(s.get_code(ADDR), s.read_code(CODE_HASH));
}

// ---------------------------------------------------------------------------
// Account state map
// ---------------------------------------------------------------------------

TEST(ZkvmAccountStateMap, CreatesOnceAndServesRepeatsFromTheLastRow)
{
    zkvm::AccountStateMap accounts{SEED, 4};
    auto const a = accounts.find_or_emplace(ADDR);
    EXPECT_TRUE(a.inserted);
    a.account_state.touched = true;
    // The repeat is the same row, not a new one.
    auto const again = accounts.find_or_emplace(ADDR);
    EXPECT_FALSE(again.inserted);
    EXPECT_EQ(&again.account_state, &a.account_state);
    EXPECT_TRUE(again.account_state.touched);
    // A switch of address must not serve the remembered row, and coming
    // back must find the first one again.
    auto const b = accounts.find_or_emplace(OTHER);
    EXPECT_TRUE(b.inserted);
    EXPECT_NE(&b.account_state, &a.account_state);
    EXPECT_FALSE(b.account_state.touched);
    auto const back = accounts.find_or_emplace(ADDR);
    EXPECT_FALSE(back.inserted);
    EXPECT_EQ(&back.account_state, &a.account_state);
    EXPECT_EQ(accounts.size(), 2u);
    size_t n = 0;
    for (auto const &kv : accounts) {
        EXPECT_TRUE(kv.first == ADDR || kv.first == OTHER);
        ++n;
    }
    EXPECT_EQ(n, 2u);
}

TEST(ZkvmAccountStateMap, RowsNeverMove)
{
    zkvm::AccountStateMap accounts{SEED, 1};
    zkvm::AccountState *const first =
        &accounts.find_or_emplace(ADDR).account_state;
    for (uint64_t i = 1; i < 4096; ++i) {
        Address a{};
        std::memcpy(a.bytes + 12, &i, sizeof(i));
        accounts.find_or_emplace(a).account_state.touched = true;
    }
    EXPECT_EQ(&accounts.find_or_emplace(ADDR).account_state, first);
}

// ---------------------------------------------------------------------------
// Slot map
// ---------------------------------------------------------------------------

TEST(ZkvmSlotMap, FindsEveryEntryAcrossTheIndexThreshold)
{
    zkvm::SlotMap<zkvm::SlotState> map{SEED};
    auto const key_at = [](size_t const i) {
        // Small numbers and keccak-shaped keys alike.
        return i % 2 == 0 ? bytes32_t{i}
                          : to_bytes(keccak256(bytes32_t{i}.bytes));
    };
    for (size_t i = 0; i < 10 * zkvm::SLOT_INDEX_FROM; ++i) {
        EXPECT_EQ(map.find(key_at(i)), nullptr);
        map.emplace(key_at(i)).current = bytes32_t{i + 1};
        EXPECT_EQ(map.size(), i + 1);
        for (size_t j = 0; j <= i; ++j) {
            auto const *const e = map.find(key_at(j));
            ASSERT_NE(e, nullptr);
            EXPECT_EQ(e->key, key_at(j));
            EXPECT_EQ(e->current, bytes32_t{j + 1});
        }
        EXPECT_EQ(map.find(bytes32_t{~uint64_t{0}}), nullptr);
    }
    size_t n = 0;
    for (auto const &e : map) {
        EXPECT_EQ(e.key, key_at(n++));
    }
    EXPECT_EQ(n, map.size());
    map.clear();
    EXPECT_TRUE(map.empty());
    EXPECT_EQ(map.find(key_at(0)), nullptr);
    map.emplace(key_at(3));
    EXPECT_NE(map.find(key_at(3)), nullptr);
}

TEST(ZkvmSlotMap, KeyEqualsComparesEveryWord)
{
    bytes32_t const k = to_bytes(keccak256(SLOT_1.bytes));
    bytes32_t same_tail = k;
    same_tail.bytes[0] ^= 1;
    bytes32_t other_tail = k;
    other_tail.bytes[31] ^= 1;
    auto const tail = zkvm::key_tail(k);
    EXPECT_TRUE(zkvm::key_equals(k, tail, k));
    EXPECT_FALSE(zkvm::key_equals(k, tail, same_tail));
    EXPECT_FALSE(zkvm::key_equals(k, tail, other_tail));
}

// ---------------------------------------------------------------------------
// Key hash
// ---------------------------------------------------------------------------

TEST(ZkvmKeyHash, SeedMovesEveryKey)
{
    // Two blocks key the tables differently, so a set of keys colliding
    // under one seed says nothing about the other.
    auto const other = zkvm::KeySeed::from_block_hash(
        0x5555555555555555666666666666666677777777777777778888888888888888_bytes32);
    EXPECT_NE(SEED, other);
    EXPECT_TRUE(SEED.seeded());
    EXPECT_FALSE(zkvm::KeySeed{}.seeded());
    EXPECT_NE(zkvm::hash_address(ADDR, SEED), zkvm::hash_address(ADDR, other));
    EXPECT_NE(
        zkvm::hash_bytes32(SLOT_1, SEED), zkvm::hash_bytes32(SLOT_1, other));
    // Keys that share a tail word still get distinct buckets.
    bytes32_t high = SLOT_1;
    high.bytes[0] = 1;
    EXPECT_EQ(zkvm::key_tail(high), zkvm::key_tail(SLOT_1));
    EXPECT_NE(zkvm::hash_bytes32(high, SEED), zkvm::hash_bytes32(SLOT_1, SEED));
}

TEST(ZkvmStateDeathTest, TablesMustShareARealSeed)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    byte_string const blob = empty_blob();
    vm::VM vm;
    auto const other = zkvm::KeySeed::from_block_hash(
        0x5555555555555555666666666666666677777777777777778888888888888888_bytes32);
    EXPECT_DEATH(
        (zkvm::State{
            mpt::OffsetTrie{blob},
            CodeTable{0, zkvm::Bytes32Hash{other}},
            vm,
            BLOCK,
            SEED}),
        "seed differs");
    EXPECT_DEATH(
        (zkvm::State{
            mpt::OffsetTrie{blob}, CodeTable{}, vm, BLOCK, zkvm::KeySeed{}}),
        "unseeded");
}

// ---------------------------------------------------------------------------
// Misuse aborts: what the shared behaviour suite cannot express, because
// only the guest has a witness that can fail to prove an account, and
// because its frame and transaction checks carry the guest's messages.
// ---------------------------------------------------------------------------

TEST(ZkvmStateDeathTest, FrameMisuseAborts)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{account_blob(ADDR, Account{.nonce = 1})};
    auto &st = f.state;
    EXPECT_DEATH(st.pop_accept(), "pop without push");
    EXPECT_DEATH(st.pop_reject(), "pop without push");
    st.push();
    EXPECT_DEATH(st.begin_transaction(0), "frame open");
    EXPECT_DEATH(st.destruct_touched_dead(), "inside a frame");
    st.pop_accept();
    st.begin_transaction(0);
    EXPECT_DEATH(st.begin_transaction(0), "out of order");
}

TEST(ZkvmStateDeathTest, WritesToUnprovenAccountsAbort)
{
    GTEST_FLAG_SET(death_test_style, "threadsafe");
    Fixture f{branch_blob(OTHER, Account{.nonce = 3}, ADDR)};
    auto &st = f.state;
    // Warmth and touch need no account; anything that reads it aborts.
    EXPECT_EQ(st.access_account(ADDR), AccessStatus::Cold);
    st.touch(ADDR);
    EXPECT_DEATH(st.set_nonce(ADDR, 1), "not in the witness");
    EXPECT_DEATH(st.add_to_balance(ADDR, 1), "not in the witness");
    EXPECT_DEATH(st.create_contract(ADDR), "not in the witness");
    EXPECT_DEATH(st.destruct_touched_dead(), "not in the witness");
}

TEST(ZkvmState, TakeLogsEmptiesTheJournal)
{
    Fixture f{account_blob(ADDR, Account{.nonce = 1})};
    auto &st = f.state;
    Receipt::Log log{};
    log.address = ADDR;
    st.store_log(log);
    ASSERT_EQ(st.logs().size(), 1u);
    auto const taken = st.take_logs();
    EXPECT_EQ(taken.size(), 1u);
    EXPECT_EQ(taken[0].address, ADDR);
    EXPECT_TRUE(st.logs().empty());
    // Which begin_transaction requires.
    st.begin_transaction(0);
}

// A re-creation inside a frame that is rejected brings the old incarnation's
// slots back, with their transaction-start values. Guest-only because the
// sequence writes a slot of a codeless account in the same transaction,
// which no EVM program can do; it pins the journal's stamp handling.
TEST(ZkvmState, RejectedRecreationRestoresSlots)
{
    Fixture f{account_blob(ADDR, Account{.nonce = 0})};
    auto &st = f.state;
    st.begin_transaction(0);
    st.set_storage(ADDR, word(5), word(7));
    st.push();
    st.create_contract(ADDR);
    EXPECT_EQ(st.get_storage(ADDR, word(5)), bytes32_t{});
    EXPECT_EQ(st.set_storage(ADDR, word(5), word(9)), StorageStatus::Added);
    st.pop_reject();
    EXPECT_EQ(st.get_storage(ADDR, word(5)), word(7));
    EXPECT_FALSE(st.is_current_incarnation(ADDR));
    // The original is still the witness value (zero), so this is a plain
    // assignment of an added slot.
    EXPECT_EQ(st.set_storage(ADDR, word(5), word(8)), StorageStatus::Assigned);
}
