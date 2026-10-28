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

#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::literals;
using namespace monad::test;

namespace
{
    using DomainBlockDbTest = OnDiskDbWithFileFixtureBase<OnDiskMachine>;

    constexpr uint64_t DOMAIN_A = 0x114eaf;
    constexpr uint64_t DOMAIN_B = 0x124eaf;

    Transaction domain_tx(uint64_t const domain, uint64_t const nonce)
    {
        return Transaction{
            .sc = {.signature = {.r = 1, .s = 1}, .chain_id = domain},
            .nonce = nonce,
            .gas_limit = 21'000,
            .to = Address{0xabc}};
    }

    // Domain block contents owned by the test, viewed by DomainBlockCommit.
    struct TestDomainBlock
    {
        uint64_t domain;
        uint64_t number;
        byte_string header;
        std::vector<Transaction> transactions;
        std::vector<Address> senders;

        DomainBlockCommit commit() const
        {
            return DomainBlockCommit{
                .domain_chain_id = domain,
                .number = number,
                .encoded_header = header,
                .transactions = transactions,
                .senders = senders};
        }
    };

    TestDomainBlock make_block(
        uint64_t const domain, uint64_t const number, size_t const tx_count)
    {
        TestDomainBlock block{
            .domain = domain,
            .number = number,
            // Opaque to the db: any bytes stand in for the header.
            .header =
                byte_string{0xc3, 0x01, static_cast<uint8_t>(number), 0x02}};
        for (size_t i = 0; i < tx_count; ++i) {
            block.transactions.push_back(domain_tx(domain, i));
            block.senders.push_back(Address{0x100 + i});
        }
        return block;
    }

    bytes32_t block_id(uint64_t const number)
    {
        return bytes32_t{number + 1};
    }

    // Commits an L1 block. `blocks` is the domain blocks derived from it, or
    // nullopt for a node that derives no private domains.
    void commit(
        TrieDb &tdb, uint64_t const number,
        std::optional<std::vector<TestDomainBlock>> const &blocks,
        bool const finalize = true)
    {
        BlockHeader const header{.number = number};
        auto builder = make_commit_builder(number, tdb);
        builder->add_state_deltas(StateDeltas{})
            .add_code(Code{})
            .add_receipts({})
            .add_transactions({}, {})
            .add_call_frames({})
            .add_ommers({});
        if (blocks.has_value()) {
            std::vector<DomainBlockCommit> commits;
            for (auto const &block : *blocks) {
                commits.push_back(block.commit());
            }
            builder->add_domain_blocks(commits);
        }
        tdb.commit(
            block_id(number),
            *builder,
            header,
            StateDeltas{},
            [&](BlockHeader &h) {
                h.state_root = tdb.state_root();
                h.receipts_root = tdb.receipts_root();
                h.transactions_root = tdb.transactions_root();
                h.withdrawals_root = tdb.withdrawals_root();
                h.ommers_hash = compute_ommers_hash({});
            });
        if (finalize) {
            tdb.finalize(number, block_id(number));
            tdb.set_block_and_prefix(number);
        }
    }

    TrieRODb read_only_at(mpt::RODb &rodb, uint64_t const number)
    {
        TrieRODb ro{rodb};
        ro.set_block_and_prefix(number);
        return ro;
    }

    std::vector<TestDomainBlock> no_domain_blocks()
    {
        return {};
    }
}

TEST_F(DomainBlockDbTest, writes_and_reads_a_domain_block)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());
    auto const block = make_block(DOMAIN_A, 5, 3);
    commit(tdb, 1, {{block}});

    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN_A), block.header);
    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN_B), std::nullopt);

    mpt::RODb rodb{mpt::ReadOnlyOnDiskDbConfig{.dbname_path = this->dbname}};
    auto ro = read_only_at(rodb, 1);
    EXPECT_EQ(ro.read_domain_block_header(DOMAIN_A), block.header);

    auto const transactions = ro.read_domain_transactions(DOMAIN_A);
    ASSERT_EQ(transactions.size(), 3);
    for (size_t i = 0; i < transactions.size(); ++i) {
        EXPECT_EQ(transactions[i].first, block.transactions[i]);
        EXPECT_EQ(transactions[i].second, block.senders[i]);
    }
    EXPECT_TRUE(ro.read_domain_transactions(DOMAIN_B).empty());

    EXPECT_EQ(ro.read_domain_block_l1_number(DOMAIN_A, 5), 1);
    EXPECT_EQ(ro.read_domain_block_l1_number(DOMAIN_A, 4), std::nullopt);
    EXPECT_EQ(ro.read_domain_block_l1_number(DOMAIN_B, 5), std::nullopt);
}

TEST_F(DomainBlockDbTest, latest_header_and_index_outlive_quiet_blocks)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());
    auto const a5 = make_block(DOMAIN_A, 5, 1);
    commit(tdb, 1, {{a5}});
    // An L1 block without domain activity.
    commit(tdb, 2, no_domain_blocks());
    // Only domain B has a block.
    auto const b0 = make_block(DOMAIN_B, 0, 0);
    commit(tdb, 3, {{b0}});
    auto const a6 = make_block(DOMAIN_A, 6, 2);
    commit(tdb, 4, {{a6}});

    mpt::RODb rodb{mpt::ReadOnlyOnDiskDbConfig{.dbname_path = this->dbname}};
    {
        auto ro = read_only_at(rodb, 2);
        // The header is the derivation cursor: still a5.
        EXPECT_EQ(ro.read_domain_block_header(DOMAIN_A), a5.header);
        // The transaction table holds this L1 block's domain blocks only.
        EXPECT_TRUE(ro.read_domain_transactions(DOMAIN_A).empty());
    }
    {
        auto ro = read_only_at(rodb, 3);
        EXPECT_EQ(ro.read_domain_block_header(DOMAIN_A), a5.header);
        EXPECT_EQ(ro.read_domain_block_header(DOMAIN_B), b0.header);
        EXPECT_TRUE(ro.read_domain_transactions(DOMAIN_A).empty());
    }
    {
        auto ro = read_only_at(rodb, 1);
        EXPECT_EQ(ro.read_domain_transactions(DOMAIN_A).size(), 1);
    }
    {
        auto ro = read_only_at(rodb, 4);
        EXPECT_EQ(ro.read_domain_block_header(DOMAIN_A), a6.header);
        EXPECT_EQ(ro.read_domain_block_header(DOMAIN_B), b0.header);
        EXPECT_EQ(ro.read_domain_transactions(DOMAIN_A).size(), 2);
        EXPECT_EQ(ro.read_domain_block_l1_number(DOMAIN_A, 5), 1);
        EXPECT_EQ(ro.read_domain_block_l1_number(DOMAIN_A, 6), 4);
        EXPECT_EQ(ro.read_domain_block_l1_number(DOMAIN_B, 0), 3);
    }
}

TEST_F(DomainBlockDbTest, proposals_see_their_own_domain_blocks)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());
    auto const a1 = make_block(DOMAIN_A, 1, 1);
    commit(tdb, 1, {{a1}});

    // An unfinalized proposal at block 2 with a domain block.
    tdb.set_block_and_prefix(1);
    auto const a2 = make_block(DOMAIN_A, 2, 1);
    commit(tdb, 2, {{a2}}, /*finalize=*/false);

    tdb.set_block_and_prefix(2, block_id(2));
    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN_A), a2.header);

    tdb.set_block_and_prefix(1);
    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN_A), a1.header);
}

TEST_F(DomainBlockDbTest, only_nodes_deriving_domains_write_domain_tables)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, std::nullopt);
    commit(tdb, 1, std::nullopt);
    EXPECT_FALSE(tdb.has_domain_tables());
    EXPECT_FALSE(this->db.find(mpt::concat(FINALIZED_NIBBLE, DOMAIN_NIBBLE), 1)
                     .has_value());

    // A node that derives private domains writes the tables with every block,
    // even one without domain blocks.
    commit(tdb, 2, no_domain_blocks());
    EXPECT_TRUE(tdb.has_domain_tables());
}

TEST_F(DomainBlockDbTest, quiet_blocks_rewrite_the_domain_tables)
{
    // The domain subtrie is rewritten with every L1 block, so compaction moves
    // it forward like an L1 table even while no domain has a block.
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());
    auto const a1 = make_block(DOMAIN_A, 1, 1);
    commit(tdb, 1, {{a1}});
    commit(tdb, 2, no_domain_blocks());
    commit(tdb, 3, no_domain_blocks());

    auto const domain =
        this->db.find(mpt::concat(FINALIZED_NIBBLE, DOMAIN_NIBBLE), 3);
    ASSERT_TRUE(domain.has_value());
    EXPECT_EQ(domain.value().node->version, 3);
    for (auto const table :
         {DOMAIN_BLOCK_HEADER_NIBBLE,
          DOMAIN_TRANSACTION_NIBBLE,
          DOMAIN_BLOCK_NUMBER_NIBBLE}) {
        auto const res = this->db.find(
            mpt::concat(FINALIZED_NIBBLE, DOMAIN_NIBBLE, table), 3);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value().node->version, 3);
    }
    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN_A), a1.header);
}
