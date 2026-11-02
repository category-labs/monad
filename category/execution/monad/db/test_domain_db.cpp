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

#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/domain_db.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <vector>

using namespace monad;

namespace
{
    constexpr uint64_t DOMAIN_A = 0x114eaf;
    constexpr uint64_t DOMAIN_B = 0x124eaf;
    Address const ADDR{0xa};
    bytes32_t const SLOT{1};
    byte_string const CODE{0x60, 0x01, 0x60, 0x00, 0x55};

    template <typename Machine>
    struct DomainDbTest : public test::OnDiskDbWithFileFixtureBase<Machine>
    {
    };

    using Machines = ::testing::Types<OnDiskMachine, MonadOnDiskMachine>;

    // Commits `l1_state` as the L1's state and `domain_state` with
    // `domain_code` as DOMAIN_A's.
    void commit(
        TrieDb &tdb, uint64_t const number, StateDeltas const &l1_state,
        StateDeltas const &domain_state, Code const &domain_code)
    {
        auto builder = make_commit_builder(number, tdb);
        std::vector const blocks{DomainBlockCommit{
            .domain_chain_id = DOMAIN_A,
            .number = number,
            .encoded_header = {},
            .transactions = {},
            .senders = {},
            .state_deltas = &domain_state,
            .code = &domain_code}};
        builder->add_state_deltas(l1_state)
            .add_code(Code{})
            .add_receipts({})
            .add_transactions({}, {})
            .add_call_frames({})
            .add_ommers({})
            .add_domain_blocks(blocks);
        tdb.commit(
            bytes32_t{number + 1},
            *builder,
            BlockHeader{.number = number},
            l1_state,
            [&](BlockHeader &h) {
                h.state_root = tdb.state_root();
                h.receipts_root = tdb.receipts_root();
                h.transactions_root = tdb.transactions_root();
                h.withdrawals_root = tdb.withdrawals_root();
                h.ommers_hash = compute_ommers_hash({});
            });
        tdb.finalize(number, bytes32_t{number + 1});
        tdb.set_block_and_prefix(number);
    }
}

TYPED_TEST_SUITE(DomainDbTest, Machines);

TYPED_TEST(DomainDbTest, state_reads_the_domain_not_the_l1)
{
    // The read cache is keyed by address alone: warm it with the L1 account.
    TrieDb tdb{this->db, true};
    auto const code_hash = to_bytes(keccak256(CODE));
    StateDeltas const l1_state{
        {ADDR,
         StateDelta{
             .account = {std::nullopt, Account{.balance = 100, .nonce = 9}},
             .storage = {{SLOT, {bytes32_t{}, bytes32_t{0x99}}}}}}};
    StateDeltas const domain_state{
        {ADDR,
         StateDelta{
             .account =
                 {std::nullopt, Account{.code_hash = code_hash, .nonce = 1}},
             .storage = {{SLOT, {bytes32_t{}, bytes32_t{0x11}}}}}}};
    Code const domain_code{{code_hash, vm::make_shared_intercode(CODE)}};
    commit(tdb, 0, l1_state, domain_state, domain_code);
    ASSERT_EQ(tdb.read_account(ADDR)->nonce, 9);

    vm::VM vm;
    DomainDb domain{tdb, DOMAIN_A};
    EXPECT_EQ(domain.state_root(), tdb.read_domain_state_root(DOMAIN_A));
    BlockState block_state{domain, vm};
    State state{block_state, Incarnation{1, 1}};
    EXPECT_EQ(state.get_nonce(ADDR), 1);
    EXPECT_EQ(state.get_balance(ADDR), 0);
    EXPECT_EQ(state.get_storage(ADDR, SLOT), bytes32_t{0x11});
    EXPECT_EQ(state.get_code_hash(ADDR), code_hash);
    auto const code = state.get_code(ADDR)->intercode();
    EXPECT_EQ(byte_string_view(code->code(), code->size()), CODE);

    DomainDb other{tdb, DOMAIN_B};
    BlockState other_block_state{other, vm};
    State other_state{other_block_state, Incarnation{1, 1}};
    EXPECT_FALSE(other_state.account_exists(ADDR));
    EXPECT_EQ(other.state_root(), NULL_ROOT);

    // The L1 still reads its own account.
    EXPECT_EQ(tdb.read_account(ADDR)->nonce, 9);
}

TYPED_TEST(DomainDbTest, reads_follow_the_wrapped_db_block)
{
    TrieDb tdb{this->db};
    StateDeltas const first{
        {ADDR,
         StateDelta{
             .account = {std::nullopt, Account{.nonce = 1}},
             .storage = {{SLOT, {bytes32_t{}, bytes32_t{0x11}}}}}}};
    commit(tdb, 0, StateDeltas{}, first, Code{});
    StateDeltas const second{
        {ADDR,
         StateDelta{
             .account = {Account{.nonce = 1}, Account{.nonce = 2}},
             .storage = {{SLOT, {bytes32_t{0x11}, bytes32_t{0x22}}}}}}};
    commit(tdb, 1, StateDeltas{}, second, Code{});

    DomainDb domain{tdb, DOMAIN_A};
    EXPECT_EQ(domain.read_account(ADDR)->nonce, 2);
    EXPECT_EQ(
        domain.read_storage(ADDR, Incarnation{0, 0}, SLOT), bytes32_t{0x22});
    tdb.set_block_and_prefix(0);
    EXPECT_EQ(domain.get_block_number(), 0);
    EXPECT_EQ(domain.read_account(ADDR)->nonce, 1);
    EXPECT_EQ(
        domain.read_storage(ADDR, Incarnation{0, 0}, SLOT), bytes32_t{0x11});
}
