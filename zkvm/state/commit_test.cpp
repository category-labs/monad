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

// Commit and the post-state root: what the trie holds once the block's
// writes are folded in. Every expectation is the root of a witness blob
// built to hold the post-state, so the trie writers are checked against
// the blob writers, which test_offset_trie.cpp checks against RLP oracles.

#include <zkvm/state/state.hpp>
#include <zkvm/state/test_witness.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <array>

using namespace monad;
using namespace monad::zkvm::test;

namespace
{
    using Shanghai = EvmTraits<EvmRevision::Shanghai>;

    bytes32_t root_of(byte_string const &blob)
    {
        return mpt::OffsetTrie{blob}.state_root();
    }

    unsigned first_nibble(bytes32_t const &slot)
    {
        return keccak256(slot.bytes).bytes[0] >> 4;
    }

    // One account whose storage holds two slots, which must hash to
    // different first nibbles so the sub-root is a branch of two leaves.
    byte_string two_slot_blob(
        Address const &addr, Account const &acct, bytes32_t const &slot_a,
        bytes32_t const &value_a, bytes32_t const &slot_b,
        bytes32_t const &value_b)
    {
        MONAD_ASSERT(first_nibble(slot_a) != first_nibble(slot_b));
        auto blob = empty_blob();
        std::array<mpt::NodeId, 16> children{};
        children[first_nibble(slot_a)] = put_slot(blob, slot_a, value_a, 1);
        children[first_nibble(slot_b)] = put_slot(blob, slot_b, value_b, 1);
        auto const storage = put_branch(blob, children);
        set_root(blob, put_account(blob, addr, acct, storage));
        return blob;
    }

    void destruct(zkvm::State &st, Address const &addr, Address const &to)
    {
        st.push();
        st.selfdestruct<Shanghai>(addr, to);
        st.pop_accept();
        st.destruct_suicides<Shanghai>();
    }
}

// ---------------------------------------------------------------------------
// Accounts
// ---------------------------------------------------------------------------

TEST(ZkvmCommit, NoWritesKeepTheWitnessRoot)
{
    Fixture f{account_blob(ADDR, Account{.balance = 10, .nonce = 7})};
    EXPECT_EQ(f.state.get_nonce(ADDR), 7);
    f.state.commit();
    EXPECT_EQ(f.state.state_root(), root_of(f.blob));
}

TEST(ZkvmCommit, WritesThatRestoreTheWitnessKeepItsRoot)
{
    Fixture f{account_blob(ADDR, Account{.balance = 10, .nonce = 7})};
    auto &st = f.state;
    st.push();
    st.set_nonce(ADDR, 8);
    st.pop_reject();
    st.set_nonce(ADDR, 7);
    st.add_to_balance(ADDR, 5);
    st.subtract_from_balance(ADDR, 5);
    st.commit();
    EXPECT_EQ(st.state_root(), root_of(f.blob));
}

TEST(ZkvmCommit, AccountUpdateRewritesTheLeaf)
{
    Fixture f{account_blob(ADDR, Account{.balance = 10, .nonce = 7})};
    auto &st = f.state;
    st.set_nonce(ADDR, 8);
    st.add_to_balance(ADDR, 5);
    st.commit();
    EXPECT_EQ(
        st.state_root(),
        root_of(account_blob(ADDR, Account{.balance = 15, .nonce = 8})));
}

TEST(ZkvmCommit, CodeSetsTheCodeHash)
{
    Fixture f{account_blob(ADDR, Account{.nonce = 1})};
    auto &st = f.state;
    st.set_code(ADDR, byte_string_view{CODE.data(), CODE.size()});
    st.commit();
    EXPECT_EQ(
        st.state_root(),
        root_of(
            account_blob(ADDR, Account{.code_hash = CODE_HASH, .nonce = 1})));
}

TEST(ZkvmCommit, NewAccountBecomesTheRootOfAnEmptyTrie)
{
    Fixture f{empty_blob()};
    auto &st = f.state;
    st.add_to_balance(ADDR, 5);
    st.commit();
    EXPECT_EQ(
        st.state_root(), root_of(account_blob(ADDR, Account{.balance = 5})));
}

TEST(ZkvmCommit, NewAccountJoinsAnExistingOne)
{
    Account const existing{.balance = 10, .nonce = 7};
    Fixture f{account_blob(ADDR, existing)};
    auto &st = f.state;
    st.add_to_balance(OTHER, 5);
    st.commit();
    EXPECT_EQ(
        st.state_root(),
        root_of(
            two_account_blob(ADDR, existing, OTHER, Account{.balance = 5})));
}

TEST(ZkvmCommit, DeletedAccountLeavesTheOtherAlone)
{
    Account const a{.balance = 10, .nonce = 7};
    Account const b{.balance = 3, .nonce = 1};
    Fixture f{two_account_blob(ADDR, a, OTHER, b)};
    auto &st = f.state;
    destruct(st, ADDR, OTHER);
    st.commit();
    EXPECT_EQ(
        st.state_root(),
        root_of(account_blob(OTHER, Account{.balance = 13, .nonce = 1})));
}

TEST(ZkvmCommit, DeletingTheOnlyAccountEmptiesTheTrie)
{
    Fixture f{account_blob(ADDR, Account{.balance = 10, .nonce = 7})};
    auto &st = f.state;
    destruct(st, ADDR, ADDR);
    st.commit();
    EXPECT_EQ(st.state_root(), root_of(empty_blob()));
}

TEST(ZkvmCommit, DeletedThenRecreatedAccountStartsOver)
{
    Fixture f{storage_blob(
        ADDR, Account{.balance = 10, .nonce = 7}, word(5), word(1))};
    auto &st = f.state;
    st.begin_transaction(0);
    destruct(st, ADDR, ADDR);
    st.begin_transaction(1);
    st.add_to_balance(ADDR, 3);
    st.commit();
    EXPECT_EQ(
        st.state_root(), root_of(account_blob(ADDR, Account{.balance = 3})));
}

// ---------------------------------------------------------------------------
// Storage
// ---------------------------------------------------------------------------

TEST(ZkvmCommit, StorageUpdateRewritesTheSlot)
{
    Account const acct{.nonce = 1};
    Fixture f{storage_blob(ADDR, acct, word(5), word(1))};
    auto &st = f.state;
    st.set_storage(ADDR, word(5), word(2));
    st.commit();
    EXPECT_EQ(
        st.state_root(), root_of(storage_blob(ADDR, acct, word(5), word(2))));
}

TEST(ZkvmCommit, StorageWriteBackToTheWitnessValueKeepsItsRoot)
{
    Account const acct{.nonce = 1};
    Fixture f{storage_blob(ADDR, acct, word(5), word(1))};
    auto &st = f.state;
    st.set_storage(ADDR, word(5), word(2));
    st.set_storage(ADDR, word(5), word(1));
    st.commit();
    EXPECT_EQ(st.state_root(), root_of(f.blob));
}

TEST(ZkvmCommit, NewSlotJoinsTheSubtree)
{
    Account const acct{.nonce = 1};
    Fixture f{storage_blob(ADDR, acct, word(5), word(1))};
    auto &st = f.state;
    st.set_storage(ADDR, word(6), word(9));
    st.commit();
    EXPECT_EQ(
        st.state_root(),
        root_of(two_slot_blob(ADDR, acct, word(5), word(1), word(6), word(9))));
}

TEST(ZkvmCommit, SlotIntoAnAccountWithoutStorage)
{
    Account const acct{.nonce = 1};
    Fixture f{account_blob(ADDR, acct)};
    auto &st = f.state;
    st.set_storage(ADDR, word(5), word(1));
    st.commit();
    EXPECT_EQ(
        st.state_root(), root_of(storage_blob(ADDR, acct, word(5), word(1))));
}

TEST(ZkvmCommit, ZeroedSlotLeavesTheSubtree)
{
    Account const acct{.nonce = 1};
    Fixture f{two_slot_blob(ADDR, acct, word(5), word(1), word(6), word(9))};
    auto &st = f.state;
    st.set_storage(ADDR, word(6), bytes32_t{});
    st.commit();
    EXPECT_EQ(
        st.state_root(), root_of(storage_blob(ADDR, acct, word(5), word(1))));
}

TEST(ZkvmCommit, ZeroingTheOnlySlotDropsTheStorageRoot)
{
    Account const acct{.nonce = 1};
    Fixture f{storage_blob(ADDR, acct, word(5), word(1))};
    auto &st = f.state;
    st.set_storage(ADDR, word(5), bytes32_t{});
    st.commit();
    EXPECT_EQ(st.state_root(), root_of(account_blob(ADDR, acct)));
}

TEST(ZkvmCommit, ZeroWriteToAnAbsentSlotChangesNothing)
{
    Account const acct{.nonce = 1};
    Fixture f{storage_blob(ADDR, acct, word(5), word(1))};
    auto &st = f.state;
    st.set_storage(ADDR, word(6), bytes32_t{});
    st.commit();
    EXPECT_EQ(st.state_root(), root_of(f.blob));
}

TEST(ZkvmCommit, SlotWrittenWithoutARead)
{
    // No SLOAD precedes the write, so the slot is hashed and resolved at
    // commit, when the witness value is needed to tell a change from a
    // rewrite.
    Account const acct{.nonce = 1};
    Fixture f{storage_blob(ADDR, acct, word(5), word(1))};
    auto &st = f.state;
    st.set_storage(ADDR, word(5), word(1));
    st.commit();
    EXPECT_EQ(st.state_root(), root_of(f.blob));
}

TEST(ZkvmCommit, RecreationDropsTheOldStorage)
{
    // EIP-684 allows the creation: no nonce, no code. The new incarnation
    // hides the witness slot, and commit starts the storage from empty.
    Fixture f{storage_blob(ADDR, Account{.balance = 4}, word(5), word(1))};
    auto &st = f.state;
    st.create_contract(ADDR);
    st.set_storage(ADDR, word(6), word(9));
    st.commit();
    EXPECT_EQ(
        st.state_root(),
        root_of(storage_blob(ADDR, Account{.balance = 4}, word(6), word(9))));
}

TEST(ZkvmCommit, RecreationWithoutWritesDropsTheStorageToo)
{
    Fixture f{storage_blob(ADDR, Account{.balance = 4}, word(5), word(1))};
    auto &st = f.state;
    st.create_contract(ADDR);
    st.commit();
    EXPECT_EQ(
        st.state_root(), root_of(account_blob(ADDR, Account{.balance = 4})));
}

TEST(ZkvmCommit, WritesAcrossTransactionsAllLand)
{
    Account const acct{.nonce = 1};
    Fixture f{account_blob(ADDR, acct)};
    auto &st = f.state;
    st.begin_transaction(0);
    st.set_storage(ADDR, word(5), word(1));
    st.begin_transaction(1);
    st.add_to_balance(OTHER, 5);
    st.commit();
    auto const slot = word(5);
    EXPECT_EQ(
        st.state_root(),
        root_of(two_account_blob(
            ADDR, acct, OTHER, Account{.balance = 5}, &slot, word(1))));
}
