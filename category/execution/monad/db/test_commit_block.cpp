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

#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/commit_block.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <optional>
#include <vector>

using namespace monad;
using namespace monad::test;

// commit_block is the runloops' single commit entry point.
TEST(CommitBlock, populates_header)
{
    using traits = MonadTraits<MONAD_TEN>;
    static_assert(traits::mip_8_active());

    mpt::Db mpt_db{std::make_unique<MonadInMemoryMachine>()};
    TrieDb tdb{mpt_db};
    ASSERT_TRUE(tdb.is_page_encoded()) << "test requires page-encoded storage";

    std::vector<Receipt> receipts;
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 21'000, .type = TransactionType::legacy});
    Receipt with_log{
        .status = 1, .gas_used = 50'000, .type = TransactionType::legacy};
    with_log.add_log(
        Receipt::Log{.topics = {bytes32_t{uint64_t{0x1}}}, .address = ADDR_A});
    receipts.push_back(std::move(with_log));

    StateDeltas const deltas{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, Account{.nonce = 1}},
             .storage = {
                 {bytes32_t{uint64_t{0x00}},
                  {bytes32_t{}, bytes32_t{uint64_t{0xaa}}}}}}}};

    BlockHeader const header{
        .number = 1, .gas_limit = 100'000, .base_fee_per_gas = 1'000};
    bytes32_t const block_id{uint64_t{1}};
    commit_block<traits>(tdb, block_id, header, deltas, Code{}, receipts);
    tdb.finalize(1, block_id);

    BlockHeader const stored = tdb.read_eth_header();
    EXPECT_EQ(stored.number, 1u);
    EXPECT_EQ(stored.gas_limit, 100'000u);

    EXPECT_EQ(stored.state_root, tdb.state_root());
    EXPECT_NE(stored.state_root, NULL_ROOT);
    EXPECT_EQ(stored.receipts_root, tdb.receipts_root());
    EXPECT_NE(stored.receipts_root, NULL_ROOT);
    EXPECT_EQ(stored.transactions_root, tdb.transactions_root());
    EXPECT_EQ(stored.transactions_root, NULL_ROOT);

    EXPECT_EQ(stored.gas_used, 50'000u) << "cumulative gas of last receipt";
    EXPECT_EQ(stored.logs_bloom, compute_bloom(receipts));
    EXPECT_NE(stored.logs_bloom, Receipt::Bloom{});

    EXPECT_EQ(
        tdb.read_storage(ADDR_A, Incarnation{0, 0}, bytes32_t{uint64_t{0x00}}),
        bytes32_t{uint64_t{0xaa}});
}
