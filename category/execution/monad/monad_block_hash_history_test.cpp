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

#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>

using namespace monad;

template <typename MonadRevisionT>
class MonadBlockHashHistoryFixture : public MonadTraitsTest<MonadRevisionT>
{
protected:
    using Trait = MonadTraitsTest<MonadRevisionT>::Trait;

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
};

DEFINE_MONAD_TRAITS_FIXTURE(MonadBlockHashHistoryFixture);

TYPED_TEST(MonadBlockHashHistoryFixture, noop_before_fork)
{
    using Trait = TestFixture::Trait;

    deploy_block_hash_history_contract<Trait>(this->state);
    if constexpr (Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(this->state.account_exists(BLOCK_HISTORY_ADDRESS));
    }
    else {
        EXPECT_TRUE(this->state.account_exists(BLOCK_HISTORY_ADDRESS));
    }

    for (size_t i = 1; i <= 128; ++i) {
        set_block_hash_history<Trait>(
            this->state,
            BlockHeader{.parent_hash = bytes32_t{i - 1}, .number = i});
    }

    for (size_t i = 1; i < 128; ++i) {
        bytes32_t const actual = get_block_hash_history(this->state, i);
        if constexpr (Trait::monad_rev() < MONAD_SIX) {
            EXPECT_EQ(actual, bytes32_t{});
        }
        else {
            EXPECT_EQ(actual, bytes32_t{i});
        }
    }
}

TYPED_TEST(MonadBlockHashHistoryFixture, redeploy)
{
    using Trait = TestFixture::Trait;

    // put bad code in state
    this->state.create_contract(BLOCK_HISTORY_ADDRESS);
    this->state.set_code(
        BLOCK_HISTORY_ADDRESS, to_byte_string_view("0xababab"));
    auto const bad_code_hash = this->state.get_code_hash(BLOCK_HISTORY_ADDRESS);

    // redeploy
    deploy_block_hash_history_contract<Trait>(this->state);

    if constexpr (Trait::monad_rev() >= MONAD_SIX) {
        EXPECT_NE(
            this->state.get_code_hash(BLOCK_HISTORY_ADDRESS), bad_code_hash);
    }
    else {
        EXPECT_EQ(
            this->state.get_code_hash(BLOCK_HISTORY_ADDRESS), bad_code_hash);
    }
}
