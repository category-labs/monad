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

#pragma once

// The behavioural spec of StateInterface, written once and run against every
// backend.
//
// A backend joins the suite by instantiating it with a Backend type:
//
//   struct Backend
//   {
//       using State = ...;             // satisfies StateInterface
//       explicit Backend(PreState const &);
//       State &state();                // the current transaction's state
//       void next_transaction();       // end it and start the next one
//   };
//
// and a Trait, the revision the trait-templated entry points run under. The
// suite is instantiated once per (Backend, Trait) pair, see Param below.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state3/state_interface.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/traits.hpp>
#include <monad/test/config.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <optional>
#include <utility>
#include <vector>

MONAD_TEST_NAMESPACE_BEGIN

// ---------------------------------------------------------------------------
// The pre-state a case starts from
// ---------------------------------------------------------------------------

struct PreAccount
{
    Address address;
    Account account;
    std::vector<std::pair<bytes32_t, bytes32_t>> storage;
};

struct PreState
{
    std::vector<PreAccount> accounts;
    // Code the pre-state carries, keyed by its keccak in the backend.
    std::vector<byte_string> codes;

    PreState &with(
        Address const &address, Account const &account,
        std::vector<std::pair<bytes32_t, bytes32_t>> storage = {})
    {
        accounts.push_back({address, account, std::move(storage)});
        return *this;
    }

    PreState &code(byte_string const &bytes)
    {
        codes.push_back(bytes);
        return *this;
    }
};

template <class B, Traits T>
struct Param
{
    using Backend = B;
    using Trait = T;
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

namespace interface_test
{
    using namespace monad::literals;

    constexpr auto A = 0x5353535353535353535353535353535353535353_address;
    constexpr auto B = 0xbebebebebebebebebebebebebebebebebebebebe_address;
    constexpr auto C = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
    constexpr auto KEY1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto KEY2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto KEY3 =
        0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
    constexpr auto VALUE1 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    constexpr auto VALUE2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
    constexpr auto VALUE3 =
        0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
    constexpr bytes32_t ZERO{};

    inline byte_string const CODE1{0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69};
    inline byte_string const CODE2{
        0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x34};
    inline bytes32_t const CODE_HASH1 = to_bytes(keccak256(CODE1));
    inline bytes32_t const CODE_HASH2 = to_bytes(keccak256(CODE2));

    inline bytes32_t word(unsigned char const n)
    {
        bytes32_t k{};
        k.bytes[31] = n;
        return k;
    }

    inline Receipt::Log log_from(Address const &address)
    {
        Receipt::Log log{};
        log.address = address;
        return log;
    }
}

// ---------------------------------------------------------------------------
// The fixture
// ---------------------------------------------------------------------------

template <class P>
class StateInterfaceTest : public ::testing::Test
{
protected:
    using Backend = typename P::Backend;
    using Trait = typename P::Trait;
    using State = typename Backend::State;

    static_assert(StateInterface<State>);

    // Build the pre-state and return the first transaction's state.
    State &given(PreState const &pre)
    {
        backend_.emplace(pre);
        return backend_->state();
    }

    State &state()
    {
        return backend_->state();
    }

    // End the current transaction and start the next; the state reference
    // a case holds may be stale afterwards, take state() again.
    void next_transaction()
    {
        backend_->next_transaction();
    }

private:
    std::optional<Backend> backend_;
};

TYPED_TEST_SUITE_P(StateInterfaceTest);

// ---------------------------------------------------------------------------
// Account reads and writes
// ---------------------------------------------------------------------------

TYPED_TEST_P(StateInterfaceTest, AccountExists)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.balance = 10'000}));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_FALSE(st.account_exists(B));
}

TYPED_TEST_P(StateInterfaceTest, GetBalance)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.balance = 10'000}));
    EXPECT_EQ(st.get_balance(A), 10'000);
    EXPECT_EQ(st.get_balance(B), 0);
    EXPECT_EQ(st.get_balance(C), 0);
}

TYPED_TEST_P(StateInterfaceTest, AddToBalance)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.balance = 1}));
    st.add_to_balance(A, 10'000);
    st.add_to_balance(B, 20'000);
    EXPECT_EQ(st.get_balance(A), 10'001);
    EXPECT_EQ(st.get_balance(B), 20'000);
    EXPECT_TRUE(st.account_exists(B));
}

TYPED_TEST_P(StateInterfaceTest, GetNonce)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 2}));
    EXPECT_EQ(st.get_nonce(A), 2);
    EXPECT_EQ(st.get_nonce(B), 0);
    EXPECT_EQ(st.get_nonce(C), 0);
}

TYPED_TEST_P(StateInterfaceTest, SetNonce)
{
    using namespace interface_test;
    auto &st = this->given(PreState{});
    st.set_nonce(B, 1);
    EXPECT_EQ(st.get_nonce(B), 1);
    EXPECT_TRUE(st.account_exists(B));
}

TYPED_TEST_P(StateInterfaceTest, GetCodeHash)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.code_hash = KEY2}));
    EXPECT_EQ(st.get_code_hash(A), KEY2);
    EXPECT_EQ(st.get_code_hash(B), NULL_HASH);
    EXPECT_EQ(st.get_code_hash(C), NULL_HASH);
}

TYPED_TEST_P(StateInterfaceTest, AccountHasCodeOrNonce)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}
                               .with(A, Account{.balance = 5})
                               .with(B, Account{.nonce = 1})
                               .with(C, Account{.code_hash = KEY2}));
    EXPECT_FALSE(st.account_has_code_or_nonce(A));
    EXPECT_TRUE(st.account_has_code_or_nonce(B));
    EXPECT_TRUE(st.account_has_code_or_nonce(C));
    EXPECT_TRUE(st.account_is_dead(A) == false);
}

TYPED_TEST_P(StateInterfaceTest, CreateContract)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}));
    st.create_contract(A);
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_TRUE(st.is_current_incarnation(A));
    // A pre-existing empty account may be created over (EIP-684).
    EXPECT_FALSE(st.is_current_incarnation(B));
    st.create_contract(B);
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_TRUE(st.is_current_incarnation(B));
}

TYPED_TEST_P(StateInterfaceTest, CreateOverConflictingAddressHidesStorage)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.balance = 18'000}, {{KEY1, VALUE1}}));
    st.create_contract(A);
    st.set_storage(A, KEY2, VALUE2);
    EXPECT_EQ(st.get_storage(A, KEY1), ZERO);
    EXPECT_EQ(st.get_storage(A, KEY2), VALUE2);
    EXPECT_EQ(st.get_balance(A), 18'000);
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

TYPED_TEST_P(StateInterfaceTest, SetCodeSetsCodeHash)
{
    using namespace interface_test;
    auto &st = this->given(PreState{});
    st.create_contract(B);
    st.set_code(B, CODE1);
    EXPECT_EQ(st.get_code_hash(B), CODE_HASH1);
}

TYPED_TEST_P(StateInterfaceTest, SetCodeAndGetCode)
{
    using namespace interface_test;
    auto &st = this->given(PreState{});
    st.create_contract(A);
    st.create_contract(B);
    st.set_code(A, CODE2);
    st.set_code(B, byte_string{});
    auto const a_icode = st.get_code(A)->intercode();
    EXPECT_EQ(byte_string_view(a_icode->code(), a_icode->size()), CODE2);
    auto const b_icode = st.get_code(B)->intercode();
    EXPECT_EQ(
        byte_string_view(b_icode->code(), b_icode->size()), byte_string{});
}

TYPED_TEST_P(StateInterfaceTest, GetCode)
{
    using namespace interface_test;
    byte_string const contract{0x60, 0x34, 0x00};
    auto &st = this->given(
        PreState{}
            .with(A, Account{.code_hash = to_bytes(keccak256(contract))})
            .code(contract));
    st.access_account(A);
    auto const c = st.get_code(A)->intercode();
    EXPECT_EQ(byte_string_view(c->code(), c->size()), contract);
    // A non-existent account has empty code.
    auto const none = st.get_code(B)->intercode();
    EXPECT_EQ(byte_string_view(none->code(), none->size()), byte_string{});
}

TYPED_TEST_P(StateInterfaceTest, GetCodeSize)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.code_hash = CODE_HASH1}).code(CODE1));
    EXPECT_EQ(st.get_code_size(A), CODE1.size());
    EXPECT_EQ(st.get_code_size(B), 0u);
}

TYPED_TEST_P(StateInterfaceTest, CopyCode)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}
                               .with(A, Account{.code_hash = CODE_HASH1})
                               .with(B, Account{.code_hash = CODE_HASH2})
                               .code(CODE1)
                               .code(CODE2));
    static constexpr unsigned size{8};
    uint8_t buffer[size];
    { // underflow
        auto const total = st.copy_code(A, 0u, buffer, size);
        EXPECT_EQ(total, CODE1.size());
        EXPECT_EQ(0, std::memcmp(buffer, CODE1.c_str(), total));
    }
    { // offset
        static constexpr auto offset = 2u;
        static constexpr auto to_copy = 3u;
        auto const total = st.copy_code(A, offset, buffer, to_copy);
        EXPECT_EQ(total, to_copy);
        EXPECT_EQ(0, std::memcmp(buffer, CODE1.c_str() + offset, total));
    }
    { // offset overflow
        static constexpr auto offset = 4u;
        auto const total = st.copy_code(A, offset, buffer, size);
        EXPECT_EQ(total, 3u);
        EXPECT_EQ(0, std::memcmp(buffer, CODE1.c_str() + offset, total));
    }
    { // regular overflow
        auto const total = st.copy_code(B, 0u, buffer, size);
        EXPECT_EQ(total, size);
        EXPECT_EQ(0, std::memcmp(buffer, CODE2.c_str(), total));
    }
    { // empty account
        EXPECT_EQ(st.copy_code(C, 0u, buffer, size), 0u);
    }
    { // offset outside size
        EXPECT_EQ(st.copy_code(A, 9, buffer, size), 0u);
    }
}

// ---------------------------------------------------------------------------
// Warmth
// ---------------------------------------------------------------------------

TYPED_TEST_P(StateInterfaceTest, AccessAccount)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.balance = 10'000}));
    EXPECT_EQ(st.access_account(A), AccessStatus::Cold);
    EXPECT_EQ(st.access_account(A), AccessStatus::Warm);
    EXPECT_EQ(st.access_account(B), AccessStatus::Cold);
    EXPECT_EQ(st.access_account(B), AccessStatus::Warm);
}

TYPED_TEST_P(StateInterfaceTest, AccessStorage)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{});
    EXPECT_EQ(st.template access_storage<Trait>(A, KEY1), AccessStatus::Cold);
    EXPECT_EQ(st.template access_storage<Trait>(A, KEY1), AccessStatus::Warm);
    EXPECT_EQ(st.template access_storage<Trait>(B, KEY1), AccessStatus::Cold);
    EXPECT_EQ(st.template access_storage<Trait>(B, KEY1), AccessStatus::Warm);
    EXPECT_EQ(st.template access_storage<Trait>(A, KEY2), AccessStatus::Cold);
    EXPECT_EQ(st.template access_storage<Trait>(A, KEY2), AccessStatus::Warm);
    EXPECT_EQ(st.template access_storage<Trait>(B, KEY2), AccessStatus::Cold);
    EXPECT_EQ(st.template access_storage<Trait>(B, KEY2), AccessStatus::Warm);
}

// ---------------------------------------------------------------------------
// Storage: reads and the EIP-2200 status of every write
// ---------------------------------------------------------------------------

TYPED_TEST_P(StateInterfaceTest, GetStorage)
{
    using namespace interface_test;
    auto &st =
        this->given(PreState{}
                        .with(A, Account{}, {{KEY1, VALUE1}, {KEY2, VALUE2}})
                        .with(B, Account{}, {{KEY1, VALUE1}}));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.get_storage(A, KEY1), VALUE1);
    EXPECT_EQ(st.get_storage(A, KEY2), VALUE2);
    EXPECT_EQ(st.get_storage(A, KEY3), ZERO);
    EXPECT_EQ(st.get_storage(B, KEY1), VALUE1);
    EXPECT_EQ(st.get_storage(B, KEY2), ZERO);
    EXPECT_EQ(st.get_storage(B, KEY3), ZERO);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageAdded)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY1, VALUE1), StorageStatus::Added);
    EXPECT_EQ(st.get_storage(B, KEY1), VALUE1);
    EXPECT_EQ(st.set_storage(B, KEY1, VALUE1), StorageStatus::Assigned);
    EXPECT_EQ(st.get_storage(B, KEY1), VALUE1);
    EXPECT_EQ(st.set_storage(B, KEY1, VALUE2), StorageStatus::Assigned);
    EXPECT_EQ(st.get_storage(B, KEY1), VALUE2);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageAddedDeleted)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY1, VALUE1), StorageStatus::Added);
    EXPECT_EQ(st.set_storage(B, KEY1, ZERO), StorageStatus::AddedDeleted);
    EXPECT_EQ(st.get_storage(B, KEY1), ZERO);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageZeroToZeroIsAssigned)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY1, ZERO), StorageStatus::Assigned);
    EXPECT_EQ(st.set_storage(B, KEY1, ZERO), StorageStatus::Assigned);
    EXPECT_EQ(st.get_storage(B, KEY1), ZERO);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageModified)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{}, {{KEY2, VALUE2}}));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_EQ(st.set_storage(A, KEY2, VALUE3), StorageStatus::Modified);
    EXPECT_EQ(st.get_storage(A, KEY2), VALUE3);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageModifiedThenAssigned)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{}, {{KEY2, VALUE2}}));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_EQ(st.set_storage(A, KEY2, VALUE3), StorageStatus::Modified);
    EXPECT_EQ(st.set_storage(A, KEY2, VALUE1), StorageStatus::Assigned);
    EXPECT_EQ(st.get_storage(A, KEY2), VALUE1);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageUnchangedIsAssigned)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{}, {{KEY2, VALUE2}}));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_EQ(st.set_storage(A, KEY2, VALUE2), StorageStatus::Assigned);
    EXPECT_EQ(st.get_storage(A, KEY2), VALUE2);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageModifiedRestored)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}, {{KEY2, VALUE2}}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY2, VALUE1), StorageStatus::Modified);
    EXPECT_EQ(st.set_storage(B, KEY2, VALUE2), StorageStatus::ModifiedRestored);
    EXPECT_EQ(st.get_storage(B, KEY2), VALUE2);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageModifiedDeleted)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}, {{KEY2, VALUE2}}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY2, VALUE1), StorageStatus::Modified);
    EXPECT_EQ(st.set_storage(B, KEY2, ZERO), StorageStatus::ModifiedDeleted);
    EXPECT_EQ(st.get_storage(B, KEY2), ZERO);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageDeleted)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}, {{KEY1, VALUE1}}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY1, ZERO), StorageStatus::Deleted);
    EXPECT_EQ(st.get_storage(B, KEY1), ZERO);
    EXPECT_EQ(st.set_storage(B, KEY1, ZERO), StorageStatus::Assigned);
    EXPECT_EQ(st.set_storage(B, KEY1, VALUE2), StorageStatus::DeletedAdded);
    EXPECT_EQ(st.get_storage(B, KEY1), VALUE2);
}

TYPED_TEST_P(StateInterfaceTest, SetStorageDeletedRestored)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(B, Account{}, {{KEY2, VALUE2}}));
    EXPECT_TRUE(st.account_exists(B));
    EXPECT_EQ(st.set_storage(B, KEY2, ZERO), StorageStatus::Deleted);
    EXPECT_EQ(st.set_storage(B, KEY2, VALUE2), StorageStatus::DeletedRestored);
    EXPECT_EQ(st.get_storage(B, KEY2), VALUE2);
}

// The full EIP-2200 walk over one pre-state slot and one fresh slot.
TYPED_TEST_P(StateInterfaceTest, StorageStatusFollowsEip2200)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.nonce = 1}, {{word(5), word(42)}}));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_EQ(st.set_storage(A, word(6), word(1)), StorageStatus::Added);
    EXPECT_EQ(st.set_storage(A, word(6), word(2)), StorageStatus::Assigned);
    EXPECT_EQ(st.set_storage(A, word(6), ZERO), StorageStatus::AddedDeleted);
    EXPECT_EQ(st.set_storage(A, word(5), word(43)), StorageStatus::Modified);
    EXPECT_EQ(
        st.set_storage(A, word(5), word(42)), StorageStatus::ModifiedRestored);
    EXPECT_EQ(st.set_storage(A, word(5), ZERO), StorageStatus::Deleted);
    EXPECT_EQ(
        st.set_storage(A, word(5), word(42)), StorageStatus::DeletedRestored);
    EXPECT_EQ(st.set_storage(A, word(5), ZERO), StorageStatus::Deleted);
    EXPECT_EQ(st.set_storage(A, word(5), word(7)), StorageStatus::DeletedAdded);
    EXPECT_EQ(st.set_storage(A, word(5), ZERO), StorageStatus::ModifiedDeleted);
}

// The EIP-2200 original is the transaction-start value: a write in an
// earlier transaction becomes the original of the next.
TYPED_TEST_P(StateInterfaceTest, TransactionStartValueFollowsWrites)
{
    using namespace interface_test;
    auto &st0 = this->given(
        PreState{}.with(A, Account{.nonce = 1}, {{word(5), word(42)}}));
    EXPECT_TRUE(st0.account_exists(A));
    EXPECT_EQ(st0.set_storage(A, word(5), word(1)), StorageStatus::Modified);
    this->next_transaction();
    auto &st = this->state();
    EXPECT_TRUE(st.account_exists(A));
    // Original 1, current 1: writing 2 is a modification, writing 1 back
    // restores.
    EXPECT_EQ(st.set_storage(A, word(5), word(2)), StorageStatus::Modified);
    EXPECT_EQ(
        st.set_storage(A, word(5), word(1)), StorageStatus::ModifiedRestored);
    // A frame that rewrites and is rejected leaves the original alone.
    st.push();
    st.set_storage(A, word(5), word(9));
    st.pop_reject();
    EXPECT_EQ(st.set_storage(A, word(5), word(2)), StorageStatus::Modified);
}

// ---------------------------------------------------------------------------
// Frames: the rollback spec
// ---------------------------------------------------------------------------

// 1. Parent writes, child accepts, parent rejects. Accepting the child keeps
// its undo records, so rejecting the parent restores the pre-frame value.
TYPED_TEST_P(StateInterfaceTest, ParentRejectUndoesAcceptedChild)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 7}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    st.set_nonce(A, 8);
    st.push();
    st.set_nonce(A, 9);
    st.pop_accept();
    EXPECT_EQ(st.get_nonce(A), 9);
    st.pop_reject();
    EXPECT_EQ(st.get_nonce(A), 7);
}

// 2. Parent writes, child rejects, parent accepts.
TYPED_TEST_P(StateInterfaceTest, ChildRejectRestoresParentValue)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 7}));
    st.push();
    st.set_nonce(A, 8);
    st.push();
    st.set_nonce(A, 9);
    st.pop_reject();
    EXPECT_EQ(st.get_nonce(A), 8);
    st.pop_accept();
    EXPECT_EQ(st.get_nonce(A), 8);
}

// 3. The same field written three times in one frame, then rejected.
TYPED_TEST_P(StateInterfaceTest, RepeatedWritesRevertToPreFrameValue)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 7}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    st.set_nonce(A, 8);
    st.set_nonce(A, 9);
    st.set_nonce(A, 10);
    st.pop_reject();
    EXPECT_EQ(st.get_nonce(A), 7);
}

// 4. An account materialised in the frame, then rejected, is absent again.
TYPED_TEST_P(StateInterfaceTest, RejectedCreationLeavesNoAccount)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 1}));
    EXPECT_FALSE(st.account_exists(C));
    st.push();
    st.add_to_balance(C, 100);
    EXPECT_TRUE(st.account_exists(C));
    st.pop_reject();
    EXPECT_FALSE(st.account_exists(C));
    EXPECT_EQ(st.get_balance(C), 0);
}

// 5. SELFDESTRUCT then revert.
TYPED_TEST_P(StateInterfaceTest, RejectedSelfdestructRestoresFlagAndBalance)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{}
                               .with(A, Account{.balance = 500, .nonce = 1})
                               .with(B, Account{.nonce = 0}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    st.template selfdestruct<Trait>(A, B);
    EXPECT_TRUE(st.is_destructed(A));
    EXPECT_EQ(st.get_balance(B), 500);
    st.pop_reject();
    EXPECT_FALSE(st.is_destructed(A));
    EXPECT_EQ(st.get_balance(A), 500);
    EXPECT_EQ(st.get_balance(B), 0);
}

// 6. Storage and transient storage.
TYPED_TEST_P(StateInterfaceTest, StorageAndTransientRevert)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.nonce = 1}, {{word(5), word(42)}}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    st.set_storage(A, word(5), word(99));
    st.set_transient_storage(A, word(6), word(77));
    EXPECT_EQ(st.get_storage(A, word(5)), word(99));
    EXPECT_EQ(st.get_transient_storage(A, word(6)), word(77));
    st.pop_reject();
    EXPECT_EQ(st.get_storage(A, word(5)), word(42));
    EXPECT_EQ(st.get_transient_storage(A, word(6)), ZERO);
}

// 7. EIP-2929: a key warmed in a frame that reverts is cold again.
TYPED_TEST_P(StateInterfaceTest, WarmthReverts)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 1}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    EXPECT_EQ(st.access_account(A), AccessStatus::Cold);
    EXPECT_EQ(st.access_account(A), AccessStatus::Warm);
    EXPECT_EQ(
        st.template access_storage<Trait>(A, word(5)), AccessStatus::Cold);
    EXPECT_EQ(
        st.template access_storage<Trait>(A, word(5)), AccessStatus::Warm);
    st.pop_reject();
    st.push();
    EXPECT_EQ(st.access_account(A), AccessStatus::Cold);
    EXPECT_EQ(
        st.template access_storage<Trait>(A, word(5)), AccessStatus::Cold);
    st.pop_accept();
}

// 8. A child rejection restores the parent's written value, not the
// pre-state's.
TYPED_TEST_P(StateInterfaceTest, ChildRejectRestoresParentSlotValue)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.nonce = 1}, {{word(5), word(42)}}));
    EXPECT_TRUE(st.account_exists(A));
    st.push();
    st.set_storage(A, word(5), word(99));
    st.push();
    st.set_storage(A, word(5), word(123));
    st.pop_reject();
    EXPECT_EQ(st.get_storage(A, word(5)), word(99));
    st.pop_accept();
    EXPECT_EQ(st.get_storage(A, word(5)), word(99));
}

// 9. Repeated writes to one slot go back to the pre-state value, not to an
// intermediate one.
TYPED_TEST_P(StateInterfaceTest, RepeatedSlotWritesRevertToPreState)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.nonce = 1}, {{word(5), word(42)}}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    st.set_storage(A, word(5), word(1));
    st.set_storage(A, word(5), word(2));
    st.set_storage(A, word(5), word(3));
    EXPECT_EQ(st.get_storage(A, word(5)), word(3));
    st.pop_reject();
    EXPECT_EQ(st.get_storage(A, word(5)), word(42));
}

// 10. A parent rejection undoes slot writes from an accepted child, both to
// a shared slot and to one only the child touched.
TYPED_TEST_P(StateInterfaceTest, ParentRejectUndoesAcceptedChildSlots)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.nonce = 1}, {{word(5), word(42)}}));
    st.set_nonce(A, st.get_nonce(A));
    st.push();
    st.set_storage(A, word(5), word(7));
    st.push();
    st.set_storage(A, word(5), word(8));
    st.set_storage(A, word(6), word(9));
    st.pop_accept();
    EXPECT_EQ(st.get_storage(A, word(5)), word(8));
    EXPECT_EQ(st.get_storage(A, word(6)), word(9));
    st.pop_reject();
    EXPECT_EQ(st.get_storage(A, word(5)), word(42));
    EXPECT_EQ(st.get_storage(A, word(6)), ZERO);
}

// 11. Nested rollback restores balances and reverses the touched transition.
TYPED_TEST_P(StateInterfaceTest, NestedBalanceAndTouched)
{
    using namespace interface_test;
    auto &st =
        this->given(PreState{}.with(A, Account{.balance = 1000, .nonce = 1}));
    EXPECT_FALSE(st.is_touched(A));
    st.access_account(A);
    st.push();
    st.add_to_balance(A, 50);
    st.push();
    st.subtract_from_balance(A, 300);
    st.add_to_balance(A, 7);
    EXPECT_EQ(st.get_balance(A), 757);
    st.pop_reject();
    EXPECT_EQ(st.get_balance(A), 1050);
    EXPECT_TRUE(st.is_touched(A));
    st.pop_reject();
    EXPECT_EQ(st.get_balance(A), 1000);
    EXPECT_FALSE(st.is_touched(A));
}

// 12. The code hash is restored after rejection.
TYPED_TEST_P(StateInterfaceTest, CodeHashReverts)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(
        A, Account{.balance = 1, .code_hash = NULL_HASH, .nonce = 1}));
    st.access_account(A);
    st.push();
    st.set_code(A, CODE1);
    EXPECT_EQ(st.get_code_hash(A), CODE_HASH1);
    EXPECT_EQ(st.get_code_size(A), CODE1.size());
    st.pop_reject();
    EXPECT_EQ(st.get_code_hash(A), NULL_HASH);
    EXPECT_EQ(st.get_code_size(A), 0u);
}

// 13. Rejecting a materialisation restores absence, not an empty account.
TYPED_TEST_P(StateInterfaceTest, RejectedMaterialisationIsAbsent)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 1}));
    EXPECT_FALSE(st.account_exists(C));
    st.access_account(C);
    st.push();
    st.set_nonce(C, 5);
    EXPECT_TRUE(st.account_exists(C));
    EXPECT_EQ(st.get_nonce(C), 5);
    st.pop_reject();
    EXPECT_FALSE(st.account_exists(C));
}

// 15. The incarnation of an existing account moved and then rejected; the
// rest of the account is left alone. (14, MIP-8 page tracking, is native
// only.)
TYPED_TEST_P(StateInterfaceTest, IncarnationChangeReverts)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(
        A, Account{.balance = 5, .code_hash = NULL_HASH, .nonce = 0}));
    EXPECT_FALSE(st.is_current_incarnation(A));
    st.access_account(A);
    st.push();
    st.set_to_state_incarnation(A);
    EXPECT_TRUE(st.is_current_incarnation(A));
    st.pop_reject();
    EXPECT_FALSE(st.is_current_incarnation(A));
    EXPECT_EQ(st.get_balance(A), 5);
}

TYPED_TEST_P(StateInterfaceTest, LogsFollowFrames)
{
    using namespace interface_test;
    auto &st = this->given(PreState{}.with(A, Account{.nonce = 1}));
    st.push();
    st.store_log(log_from(A));
    st.push();
    st.store_log(log_from(B));
    st.pop_reject();
    EXPECT_EQ(st.logs().size(), 1u);
    st.push();
    st.store_log(log_from(B));
    st.pop_accept();
    st.pop_accept();
    ASSERT_EQ(st.logs().size(), 2u);
    EXPECT_EQ(st.logs()[0].address, A);
    EXPECT_EQ(st.logs()[1].address, B);
    this->next_transaction();
    EXPECT_TRUE(this->state().logs().empty());
}

// ---------------------------------------------------------------------------
// The transaction boundary
// ---------------------------------------------------------------------------

TYPED_TEST_P(StateInterfaceTest, TransactionBoundaryResetsScope)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st0 = this->given(PreState{}.with(A, Account{.nonce = 1}));
    EXPECT_EQ(st0.access_account(A), AccessStatus::Cold);
    EXPECT_EQ(
        st0.template access_storage<Trait>(A, word(5)), AccessStatus::Cold);
    st0.touch(A);
    st0.set_transient_storage(A, word(1), word(2));
    st0.set_nonce(A, 4);
    EXPECT_TRUE(st0.is_touched(A));
    this->next_transaction();
    auto &st = this->state();
    // Warmth, touched and transient storage are per transaction; the nonce
    // is not.
    EXPECT_EQ(st.access_account(A), AccessStatus::Cold);
    EXPECT_EQ(
        st.template access_storage<Trait>(A, word(5)), AccessStatus::Cold);
    EXPECT_FALSE(st.is_touched(A));
    EXPECT_EQ(st.get_transient_storage(A, word(1)), ZERO);
    EXPECT_EQ(st.get_nonce(A), 4);
    EXPECT_FALSE(st.is_current_incarnation(C));
}

// ---------------------------------------------------------------------------
// SELFDESTRUCT and the end-of-transaction walks
// ---------------------------------------------------------------------------

// The returned pair is (first destruct of this account, balance moved); the
// beneficiary is credited at once and the account itself settles at the
// end of the transaction under the revision's rule.
TYPED_TEST_P(StateInterfaceTest, Selfdestruct)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{}
                               .with(A, Account{.balance = 18'000})
                               .with(C, Account{.balance = 38'000}));
    st.create_contract(B);
    st.add_to_balance(B, 28'000);

    EXPECT_EQ(
        st.template selfdestruct<Trait>(A, C), std::make_pair(true, 18'000));
    EXPECT_EQ(st.get_balance(A), 0);
    EXPECT_EQ(st.get_balance(C), 56'000);
    EXPECT_EQ(st.template selfdestruct<Trait>(A, C), std::make_pair(false, 0));

    EXPECT_EQ(
        st.template selfdestruct<Trait>(B, C), std::make_pair(true, 28'000));
    EXPECT_EQ(st.get_balance(B), 0);
    EXPECT_EQ(st.get_balance(C), 84'000);
    EXPECT_EQ(st.template selfdestruct<Trait>(B, C), std::make_pair(false, 0));

    st.template destruct_suicides<Trait>();
    // A pre-state account survives under EIP-6780; one created in this
    // transaction never does.
    if constexpr (Trait::eip_6780_active()) {
        EXPECT_TRUE(st.account_exists(A));
    }
    else {
        EXPECT_FALSE(st.account_exists(A));
    }
    EXPECT_FALSE(st.account_exists(B));
}

TYPED_TEST_P(StateInterfaceTest, SelfdestructCreatedInTransaction)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{}.with(C, Account{.balance = 38'000}));
    st.create_contract(A);
    st.add_to_balance(A, 18'000);
    EXPECT_EQ(
        st.template selfdestruct<Trait>(A, C), std::make_pair(true, 18'000));
    EXPECT_EQ(st.get_balance(A), 0);
    EXPECT_EQ(st.get_balance(C), 56'000);
    EXPECT_EQ(st.template selfdestruct<Trait>(A, C), std::make_pair(false, 0));
    st.template destruct_suicides<Trait>();
    EXPECT_FALSE(st.account_exists(A));
}

// Balance is burned when the beneficiary is the account itself, before
// EIP-6780; the returned value is the balance read before the guard, which
// is what the call tracer records.
TYPED_TEST_P(StateInterfaceTest, SelfdestructToSelfOfPreStateAccount)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{}.with(A, Account{.balance = 18'000}));
    EXPECT_EQ(
        st.template selfdestruct<Trait>(A, A), std::make_pair(true, 18'000));
    uint256_t const after = st.get_balance(A);
    st.template destruct_suicides<Trait>();
    if constexpr (!Trait::eip_6780_active()) {
        EXPECT_EQ(after, 0);
        EXPECT_FALSE(st.account_exists(A));
    }
    else {
        EXPECT_EQ(after, 18'000);
        EXPECT_TRUE(st.account_exists(A));
    }
}

TYPED_TEST_P(StateInterfaceTest, SelfdestructToSelfCreatedInTransaction)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{});
    st.create_contract(A);
    st.add_to_balance(A, 18'000);
    EXPECT_EQ(
        st.template selfdestruct<Trait>(A, A), std::make_pair(true, 18'000));
    if constexpr (Trait::eip_8246_active()) {
        // No burn: the account keeps its balance and loses the rest.
        EXPECT_EQ(st.get_balance(A), 18'000);
        st.template destruct_suicides<Trait>();
        ASSERT_TRUE(st.account_exists(A));
        EXPECT_EQ(st.get_balance(A), 18'000);
        EXPECT_EQ(st.get_nonce(A), 0);
        EXPECT_EQ(st.get_code_hash(A), NULL_HASH);
    }
    else {
        EXPECT_EQ(st.get_balance(A), 0);
        st.template destruct_suicides<Trait>();
        EXPECT_FALSE(st.account_exists(A));
    }
}

TYPED_TEST_P(StateInterfaceTest, SelfdestructToSelfWithZeroBalance)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{});
    // Empty after the destruct, so EIP-161 deletes it at every revision.
    st.create_contract(A);
    EXPECT_EQ(st.template selfdestruct<Trait>(A, A), std::make_pair(true, 0));
    st.template destruct_suicides<Trait>();
    EXPECT_FALSE(st.account_exists(A));
}

TYPED_TEST_P(StateInterfaceTest, SelfdestructMutualConservesSupply)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{});
    st.create_contract(A);
    st.set_nonce(A, 1);
    st.set_code(A, CODE1);
    st.add_to_balance(A, 100);
    st.create_contract(B);
    st.set_nonce(B, 1);
    st.set_code(B, CODE2);
    st.add_to_balance(B, 200);

    st.template selfdestruct<Trait>(A, B);
    EXPECT_EQ(st.get_balance(A), 0);
    EXPECT_EQ(st.get_balance(B), 300);
    st.template selfdestruct<Trait>(B, A);
    EXPECT_EQ(st.get_balance(A), 300);
    EXPECT_EQ(st.get_balance(B), 0);

    st.template destruct_suicides<Trait>();
    st.destruct_touched_dead();
    if constexpr (Trait::eip_8246_active()) {
        ASSERT_TRUE(st.account_exists(A));
        EXPECT_EQ(st.get_balance(A), 300);
        EXPECT_EQ(st.get_nonce(A), 0);
        EXPECT_EQ(st.get_code_hash(A), NULL_HASH);
    }
    else {
        EXPECT_FALSE(st.account_exists(A));
    }
    EXPECT_FALSE(st.account_exists(B));
}

// A pre-state account created over, written and destructed to itself in
// one transaction: what the next transaction of the block sees.
TYPED_TEST_P(StateInterfaceTest, SelfdestructPreservedStorageZeroed)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st0 = this->given(
        PreState{}.with(A, Account{.balance = 18'000}, {{KEY1, VALUE1}}));
    // create_contract makes the pre-existing account same-transaction for
    // EIP-6780.
    st0.create_contract(A);
    st0.set_storage(A, KEY2, VALUE2);
    EXPECT_EQ(
        st0.template selfdestruct<Trait>(A, A), std::make_pair(true, 18'000));
    st0.template destruct_suicides<Trait>();
    this->next_transaction();
    auto &st = this->state();
    if constexpr (Trait::eip_8246_active()) {
        // Both slots read as zero: KEY2 because the settlement zeroed it,
        // KEY1 because create_contract moved the incarnation.
        ASSERT_TRUE(st.account_exists(A));
        EXPECT_EQ(st.get_balance(A), 18'000);
        EXPECT_EQ(st.get_nonce(A), 0);
        EXPECT_EQ(st.get_code_hash(A), NULL_HASH);
        EXPECT_EQ(st.get_storage(A, KEY1), ZERO);
        EXPECT_EQ(st.get_storage(A, KEY2), ZERO);
    }
    else {
        EXPECT_FALSE(st.account_exists(A));
    }
}

TYPED_TEST_P(StateInterfaceTest, DestructSuicidesOnlyCreatedInTransaction)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(PreState{}
                               .with(A, Account{.balance = 500, .nonce = 1})
                               .with(B, Account{.nonce = 0}));
    st.push();
    st.template selfdestruct<Trait>(A, B);
    st.create_contract(C);
    st.add_to_balance(C, 7);
    st.set_storage(C, word(1), word(1));
    st.template selfdestruct<Trait>(C, B);
    st.pop_accept();
    st.template destruct_suicides<Trait>();
    if constexpr (Trait::eip_6780_active()) {
        EXPECT_TRUE(st.account_exists(A));
        EXPECT_EQ(st.get_balance(A), 0);
    }
    else {
        EXPECT_FALSE(st.account_exists(A));
    }
    EXPECT_FALSE(st.account_exists(C));
    EXPECT_EQ(st.get_balance(B), 507);
}

TYPED_TEST_P(StateInterfaceTest, DestructTouchedDead)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st = this->given(
        PreState{}.with(A, Account{.balance = 10'000}).with(B, Account{}));
    EXPECT_TRUE(st.account_exists(A));
    st.destruct_touched_dead();
    st.template destruct_suicides<Trait>();
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_TRUE(st.account_exists(B));

    st.subtract_from_balance(A, 10'000);
    st.destruct_touched_dead();
    st.template destruct_suicides<Trait>();
    EXPECT_FALSE(st.account_exists(A));
    EXPECT_TRUE(st.account_exists(B));

    st.touch(B);
    st.destruct_touched_dead();
    st.template destruct_suicides<Trait>();
    EXPECT_FALSE(st.account_exists(B));

    st.add_to_balance(A, 0);
    EXPECT_TRUE(st.account_exists(A));
    st.destruct_touched_dead();
    st.template destruct_suicides<Trait>();
    EXPECT_FALSE(st.account_exists(A));

    st.subtract_from_balance(A, 0);
    EXPECT_TRUE(st.account_exists(A));
    st.destruct_touched_dead();
    st.template destruct_suicides<Trait>();
    EXPECT_FALSE(st.account_exists(A));
}

TYPED_TEST_P(StateInterfaceTest, DestructTouchedDeadSparesTheUntouched)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.balance = 1}).with(B, Account{.nonce = 0}));
    // B is empty and touched by a zero transfer; A has balance; C is
    // touched without ever being materialised.
    st.add_to_balance(B, 0);
    st.add_to_balance(A, 0);
    st.touch(C);
    st.destruct_touched_dead();
    EXPECT_FALSE(st.account_exists(B));
    EXPECT_TRUE(st.account_exists(A));
    EXPECT_FALSE(st.account_exists(C));
}

// ---------------------------------------------------------------------------
// Re-creation
// ---------------------------------------------------------------------------

// Re-creation hides the slots of the earlier incarnation: the CREATE2,
// SSTORE, SELFDESTRUCT, CREATE2, SSTORE sequence across two transactions.
TYPED_TEST_P(StateInterfaceTest, RecreatedAccountStartsWithEmptyStorage)
{
    using namespace interface_test;
    using Trait = typename TestFixture::Trait;
    auto &st0 = this->given(PreState{}.with(A, Account{.nonce = 1}));
    st0.push();
    st0.create_contract(C);
    EXPECT_EQ(st0.set_storage(C, word(5), word(7)), StorageStatus::Added);
    st0.template selfdestruct<Trait>(C, A);
    st0.pop_accept();
    st0.template destruct_suicides<Trait>();
    EXPECT_FALSE(st0.account_exists(C));

    this->next_transaction();
    auto &st = this->state();
    st.push();
    st.create_contract(C);
    EXPECT_EQ(st.get_storage(C, word(5)), ZERO);
    // A fresh store, charged as such: the original is zero, not 7.
    EXPECT_EQ(st.set_storage(C, word(5), word(9)), StorageStatus::Added);
    EXPECT_EQ(st.get_storage(C, word(5)), word(9));
    st.pop_reject();
    // The rejected re-creation leaves the account absent again.
    EXPECT_FALSE(st.account_exists(C));
}

// A pre-state account with nonce 0 and no code may be CREATEd over
// (EIP-684): the new incarnation hides its storage, and a rejected creation
// restores the old incarnation with the account otherwise untouched.
TYPED_TEST_P(StateInterfaceTest, RejectedRecreationRestoresIncarnation)
{
    using namespace interface_test;
    auto &st = this->given(
        PreState{}.with(A, Account{.balance = 3}, {{word(5), word(7)}}));
    EXPECT_FALSE(st.is_current_incarnation(A));
    st.push();
    st.create_contract(A);
    EXPECT_TRUE(st.is_current_incarnation(A));
    EXPECT_EQ(st.get_storage(A, word(5)), ZERO);
    EXPECT_EQ(st.set_storage(A, word(5), word(9)), StorageStatus::Added);
    st.pop_reject();
    EXPECT_FALSE(st.is_current_incarnation(A));
    EXPECT_EQ(st.get_balance(A), 3);
    EXPECT_TRUE(st.account_exists(A));
}

REGISTER_TYPED_TEST_SUITE_P(
    StateInterfaceTest, AccountExists, GetBalance, AddToBalance, GetNonce,
    SetNonce, GetCodeHash, AccountHasCodeOrNonce, CreateContract,
    CreateOverConflictingAddressHidesStorage, SetCodeSetsCodeHash,
    SetCodeAndGetCode, GetCode, GetCodeSize, CopyCode, AccessAccount,
    AccessStorage, GetStorage, SetStorageAdded, SetStorageAddedDeleted,
    SetStorageZeroToZeroIsAssigned, SetStorageModified,
    SetStorageModifiedThenAssigned, SetStorageUnchangedIsAssigned,
    SetStorageModifiedRestored, SetStorageModifiedDeleted, SetStorageDeleted,
    SetStorageDeletedRestored, StorageStatusFollowsEip2200,
    TransactionStartValueFollowsWrites, ParentRejectUndoesAcceptedChild,
    ChildRejectRestoresParentValue, RepeatedWritesRevertToPreFrameValue,
    RejectedCreationLeavesNoAccount, RejectedSelfdestructRestoresFlagAndBalance,
    StorageAndTransientRevert, WarmthReverts,
    ChildRejectRestoresParentSlotValue, RepeatedSlotWritesRevertToPreState,
    ParentRejectUndoesAcceptedChildSlots, NestedBalanceAndTouched,
    CodeHashReverts, RejectedMaterialisationIsAbsent, IncarnationChangeReverts,
    LogsFollowFrames, TransactionBoundaryResetsScope, Selfdestruct,
    SelfdestructCreatedInTransaction, SelfdestructToSelfOfPreStateAccount,
    SelfdestructToSelfCreatedInTransaction, SelfdestructToSelfWithZeroBalance,
    SelfdestructMutualConservesSupply, SelfdestructPreservedStorageZeroed,
    DestructSuicidesOnlyCreatedInTransaction, DestructTouchedDead,
    DestructTouchedDeadSparesTheUntouched,
    RecreatedAccountStartsWithEmptyStorage,
    RejectedRecreationRestoresIncarnation);

MONAD_TEST_NAMESPACE_END
