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
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
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
          DOMAIN_BLOCK_NUMBER_NIBBLE,
          DOMAIN_STATE_NIBBLE,
          DOMAIN_CODE_NIBBLE,
          DOMAIN_RECEIPT_NIBBLE,
          DOMAIN_FINALIZED_HEADER_NIBBLE}) {
        auto const res = this->db.find(
            mpt::concat(FINALIZED_NIBBLE, DOMAIN_NIBBLE, table), 3);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(res.value().node->version, 3);
    }
    EXPECT_EQ(tdb.read_domain_block_header(DOMAIN_A), a1.header);
}

namespace
{
    template <typename Machine>
    struct DomainStateDbTest : public OnDiskDbWithFileFixtureBase<Machine>
    {
    };

    using Machines = ::testing::Types<OnDiskMachine, MonadOnDiskMachine>;

    Address const ADDR_A{0xa};
    Address const ADDR_B{0xb};
    // In the same storage page.
    bytes32_t const SLOT_1{1};
    bytes32_t const SLOT_2{2};

    // Commits an L1 block with `l1_state` and the given domain blocks, whose
    // finalized headers are added between the two commit stages.
    void commit_executed(
        TrieDb &tdb, uint64_t const number, StateDeltas const &l1_state,
        std::span<DomainBlockCommit const> const blocks,
        std::span<DomainHeaderCommit const> const headers = {})
    {
        auto builder = make_commit_builder(number, tdb);
        builder->add_state_deltas(l1_state)
            .add_code(Code{})
            .add_receipts({})
            .add_transactions({}, {})
            .add_call_frames({})
            .add_ommers({})
            .add_domain_blocks(blocks);
        tdb.commit(
            block_id(number),
            *builder,
            BlockHeader{.number = number},
            l1_state,
            [&](BlockHeader &h) {
                h.state_root = tdb.state_root();
                h.receipts_root = tdb.receipts_root();
                h.transactions_root = tdb.transactions_root();
                h.withdrawals_root = tdb.withdrawals_root();
                h.ommers_hash = compute_ommers_hash({});
                builder->add_domain_finalized_headers(headers);
            });
        tdb.finalize(number, block_id(number));
        tdb.set_block_and_prefix(number);
    }

    DomainBlockCommit executed_block(
        uint64_t const domain, uint64_t const number, StateDeltas const &state,
        Code const &code = Code{}, std::span<Receipt const> const receipts = {})
    {
        return DomainBlockCommit{
            .domain_chain_id = domain,
            .number = number,
            .encoded_header = {},
            .transactions = {},
            .senders = {},
            .state_deltas = &state,
            .code = &code,
            .receipts = receipts};
    }

    bytes32_t read_domain_slot(
        TrieDb &tdb, uint64_t const domain, Address const &addr,
        bytes32_t const &slot)
    {
        if (tdb.is_page_encoded()) {
            return tdb.read_domain_storage(
                domain,
                addr,
                compute_page_key(slot))[compute_slot_offset(slot)];
        }
        return tdb.read_domain_storage(domain, addr, slot)[0];
    }

    StateDeltas two_accounts()
    {
        return StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 7, .nonce = 1}},
                 .storage =
                     {{SLOT_1, {bytes32_t{}, bytes32_t{0x11}}},
                      {SLOT_2, {bytes32_t{}, bytes32_t{0x22}}}}}},
            {ADDR_B,
             StateDelta{.account = {std::nullopt, Account{.nonce = 3}}}}};
    }
}

TYPED_TEST_SUITE(DomainStateDbTest, Machines);

TYPED_TEST(DomainStateDbTest, domain_state_has_the_root_l1_state_would)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());

    auto const state = two_accounts();
    std::vector const blocks{executed_block(DOMAIN_A, 0, state)};
    commit_executed(tdb, 1, StateDeltas{}, blocks);

    // The domain's state is in its own tries, apart from the L1's.
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
    EXPECT_EQ(tdb.read_account(ADDR_A), std::nullopt);
    EXPECT_EQ(
        tdb.read_domain_account(DOMAIN_A, ADDR_A),
        (Account{.balance = 7, .nonce = 1}));
    EXPECT_EQ(tdb.read_domain_account(DOMAIN_B, ADDR_A), std::nullopt);
    EXPECT_EQ(read_domain_slot(tdb, DOMAIN_A, ADDR_A, SLOT_1), bytes32_t{0x11});
    EXPECT_EQ(read_domain_slot(tdb, DOMAIN_A, ADDR_A, SLOT_2), bytes32_t{0x22});
    EXPECT_EQ(read_domain_slot(tdb, DOMAIN_B, ADDR_A, SLOT_1), bytes32_t{});
    auto const domain_root = tdb.read_domain_state_root(DOMAIN_A);
    EXPECT_NE(domain_root, NULL_ROOT);
    EXPECT_EQ(tdb.read_domain_state_root(DOMAIN_B), NULL_ROOT);

    // The same state committed to the L1 gets the same root.
    commit_executed(tdb, 2, state, {});
    EXPECT_EQ(tdb.state_root(), domain_root);
    EXPECT_EQ(tdb.read_domain_state_root(DOMAIN_A), domain_root);
}

TYPED_TEST(DomainStateDbTest, domain_storage_updates_read_the_domain_state)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());
    StateDeltas const first{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, Account{.nonce = 1}},
             .storage = {{SLOT_1, {bytes32_t{}, bytes32_t{0x11}}}}}}};
    std::vector const block1{executed_block(DOMAIN_A, 0, first)};
    commit_executed(tdb, 1, StateDeltas{}, block1);

    // A later write to the same page keeps the earlier slot.
    StateDeltas const second{
        {ADDR_A,
         StateDelta{
             .account = {Account{.nonce = 1}, Account{.nonce = 2}},
             .storage = {{SLOT_2, {bytes32_t{}, bytes32_t{0x22}}}}}}};
    std::vector const block2{executed_block(DOMAIN_A, 1, second)};
    commit_executed(tdb, 2, StateDeltas{}, block2);

    EXPECT_EQ(read_domain_slot(tdb, DOMAIN_A, ADDR_A, SLOT_1), bytes32_t{0x11});
    EXPECT_EQ(read_domain_slot(tdb, DOMAIN_A, ADDR_A, SLOT_2), bytes32_t{0x22});
    EXPECT_EQ(tdb.read_domain_account(DOMAIN_A, ADDR_A), Account{.nonce = 2});

    // Same root as the same two blocks on the L1.
    auto const domain_root = tdb.read_domain_state_root(DOMAIN_A);
    commit_executed(tdb, 3, first, {});
    commit_executed(tdb, 4, second, {});
    EXPECT_EQ(tdb.state_root(), domain_root);
}

TEST_F(DomainBlockDbTest, domain_code_and_receipts_stay_in_the_domain)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());

    byte_string const code{0x60, 0x00, 0x60, 0x00, 0xf3};
    auto const code_hash = to_bytes(keccak256(code));
    Code const domain_code{{code_hash, vm::make_shared_intercode(code)}};
    Receipt first{.status = 1, .gas_used = 21'000};
    first.add_log(Receipt::Log{.data = {0x01}, .address = ADDR_A});
    Receipt const second{.status = 0, .gas_used = 21'000};
    std::vector const receipts{first, second};
    StateDeltas const state{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, Account{.code_hash = code_hash}}}}};
    auto const transactions = make_block(DOMAIN_A, 0, 2);
    auto block = executed_block(DOMAIN_A, 0, state, domain_code, receipts);
    block.encoded_header = transactions.header;
    block.transactions = transactions.transactions;
    block.senders = transactions.senders;
    commit_executed(tdb, 1, StateDeltas{}, std::vector{block});

    EXPECT_EQ(
        byte_string_view(
            tdb.read_domain_code(DOMAIN_A, code_hash)->code(),
            tdb.read_domain_code(DOMAIN_A, code_hash)->size()),
        code);
    EXPECT_EQ(tdb.read_code(code_hash)->size(), 0);
    EXPECT_EQ(tdb.read_domain_code(DOMAIN_B, code_hash)->size(), 0);

    // Receipts are replaced with each L1 block, like the transactions.
    commit(tdb, 2, no_domain_blocks());
    mpt::RODb rodb{mpt::ReadOnlyOnDiskDbConfig{.dbname_path = this->dbname}};
    EXPECT_EQ(read_only_at(rodb, 1).read_domain_receipts(DOMAIN_A), receipts);
    EXPECT_TRUE(read_only_at(rodb, 2).read_domain_receipts(DOMAIN_A).empty());
    // Code and state persist.
    EXPECT_EQ(tdb.read_domain_code(DOMAIN_A, code_hash)->size(), code.size());
}

TEST_F(DomainBlockDbTest, keeps_the_last_finalized_headers)
{
    TrieDb tdb{this->db};
    commit(tdb, 0, no_domain_blocks());
    StateDeltas const no_state;
    auto const header = [](uint64_t const number) {
        // Opaque to the db: any bytes stand in for the header.
        byte_string encoded{0xc9, 0x88};
        for (unsigned i = 0; i < 8; ++i) {
            encoded.push_back(static_cast<uint8_t>(number >> (56 - 8 * i)));
        }
        return encoded;
    };
    uint64_t const last = BlockHashBuffer::N;
    for (uint64_t number = 0; number <= last; ++number) {
        auto const encoded = header(number);
        std::vector const blocks{executed_block(DOMAIN_A, number, no_state)};
        std::vector const headers{DomainHeaderCommit{
            .domain_chain_id = DOMAIN_A,
            .number = number,
            .encoded_header = encoded}};
        commit_executed(tdb, number + 1, StateDeltas{}, blocks, headers);
    }

    EXPECT_EQ(tdb.read_domain_finalized_header(DOMAIN_A, 0), std::nullopt);
    EXPECT_EQ(tdb.read_domain_finalized_header(DOMAIN_A, 1), header(1));
    EXPECT_EQ(tdb.read_domain_finalized_header(DOMAIN_A, last), header(last));
    EXPECT_EQ(tdb.read_domain_finalized_header(DOMAIN_B, last), std::nullopt);

    mpt::RODb rodb{mpt::ReadOnlyOnDiskDbConfig{.dbname_path = this->dbname}};
    EXPECT_EQ(
        read_only_at(rodb, 1).read_domain_finalized_header(DOMAIN_A, 0),
        header(0));
}
