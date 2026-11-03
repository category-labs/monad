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

#include <category/execution/domain/l1_source.hpp>

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/util.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>
#include <string>
#include <unistd.h>
#include <vector>

using namespace monad;
using namespace monad::domain;

namespace
{
    Receipt receipt(uint64_t const gas_used, uint64_t const tag)
    {
        Receipt receipt{
            .status = 1,
            .gas_used = gas_used,
            .type = TransactionType::eip1559};
        receipt.add_log(Receipt::Log{
            .data = byte_string(1, static_cast<unsigned char>(tag)),
            .topics = {bytes32_t{tag}},
            .address = Address{tag}});
        return receipt;
    }

    // An L1 node's triedb on a temporary file, keeping the shortest history.
    class PrivateDomainL1Source : public ::testing::Test
    {
    protected:
        std::string path_ =
            (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
             "private_domain_l1_source_XXXXXX")
                .string();
        std::optional<mpt::Db> mpt_db_;
        std::optional<TrieDb> db_;

        void SetUp() override
        {
            int const fd = ::mkstemp(path_.data());
            ASSERT_NE(fd, -1);
            ASSERT_NE(
                ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)),
                -1);
            ::close(fd);
            mpt_db_.emplace(
                std::make_unique<MonadOnDiskMachine>(),
                mpt::OnDiskDbConfig{
                    .append = false,
                    .dbname_path = path_,
                    .fixed_history_length = mpt::MIN_HISTORY_LENGTH,
                    .chunk_capacity = 24});
            db_.emplace(*mpt_db_);
        }

        void TearDown() override
        {
            db_.reset();
            mpt_db_.reset();
            std::filesystem::remove(path_);
        }

        void
        commit(uint64_t const number, std::vector<Receipt> const &receipts = {})
        {
            test::commit_sequential(
                *db_,
                {},
                {},
                BlockHeader{.number = number, .timestamp = 1'000 + number},
                receipts);
        }
    };
}

TEST_F(PrivateDomainL1Source, has_no_finalized_block_on_an_empty_db)
{
    TrieDbL1Source const source{*mpt_db_};
    EXPECT_EQ(source.latest_finalized(), mpt::INVALID_BLOCK_NUM);
    auto const header = source.read_finalized_header(0);
    ASSERT_TRUE(header.has_error());
    EXPECT_EQ(header.error(), mpt::DbError::version_no_longer_exist);
    auto const receipts = source.read_finalized_receipts(0);
    ASSERT_TRUE(receipts.has_error());
    EXPECT_EQ(receipts.error(), mpt::DbError::version_no_longer_exist);
}

TEST_F(PrivateDomainL1Source, reads_header_and_receipts)
{
    std::vector const receipts{receipt(21'000, 1), receipt(50'000, 2)};
    commit(0);
    commit(1, receipts);
    commit(2);

    TrieDbL1Source const source{*mpt_db_};
    EXPECT_EQ(source.latest_finalized(), 2);

    auto const header = source.read_finalized_header(1);
    ASSERT_TRUE(header.has_value());
    EXPECT_EQ(header.value().number, 1);
    EXPECT_EQ(header.value().timestamp, 1'001);
    auto const read = source.read_finalized_receipts(1);
    ASSERT_TRUE(read.has_value());
    EXPECT_EQ(read.value(), receipts);

    auto const empty = source.read_finalized_receipts(2);
    ASSERT_TRUE(empty.has_value());
    EXPECT_TRUE(empty.value().empty());
}

TEST_F(PrivateDomainL1Source, fails_past_the_latest_finalized_block)
{
    commit(0);
    commit(1);

    TrieDbL1Source const source{*mpt_db_};
    EXPECT_EQ(source.latest_finalized(), 1);
    auto const header = source.read_finalized_header(2);
    ASSERT_TRUE(header.has_error());
    EXPECT_EQ(header.error(), mpt::DbError::version_no_longer_exist);
    auto const receipts = source.read_finalized_receipts(2);
    ASSERT_TRUE(receipts.has_error());
    EXPECT_EQ(receipts.error(), mpt::DbError::version_no_longer_exist);
}

TEST_F(PrivateDomainL1Source, fails_once_a_block_leaves_history)
{
    for (uint64_t number = 0; number <= mpt::MIN_HISTORY_LENGTH; ++number) {
        commit(number, {receipt(21'000, 1)});
    }
    ASSERT_EQ(mpt_db_->get_earliest_version(), 1);

    TrieDbL1Source const source{*mpt_db_};
    auto const header = source.read_finalized_header(0);
    ASSERT_TRUE(header.has_error());
    EXPECT_EQ(header.error(), mpt::DbError::version_no_longer_exist);
    auto const receipts = source.read_finalized_receipts(0);
    ASSERT_TRUE(receipts.has_error());
    EXPECT_EQ(receipts.error(), mpt::DbError::version_no_longer_exist);
    EXPECT_TRUE(source.read_finalized_header(1).has_value());
    EXPECT_TRUE(source.read_finalized_receipts(1).has_value());
}

TEST_F(PrivateDomainL1Source, reads_storage_as_of_a_block)
{
    Address const contract{0xc0};
    bytes32_t const slot{7};
    Account const account{.nonce = 1};
    test::commit_sequential(*db_, {}, {}, BlockHeader{.number = 0});
    test::commit_sequential(
        *db_,
        StateDeltas{
            {contract,
             StateDelta{
                 .account = {std::nullopt, account},
                 .storage = {{slot, {bytes32_t{}, bytes32_t{1}}}}}}},
        {},
        BlockHeader{.number = 1});
    test::commit_sequential(
        *db_,
        StateDeltas{
            {contract,
             StateDelta{
                 .account = {account, account},
                 .storage = {{slot, {bytes32_t{1}, bytes32_t{2}}}}}}},
        {},
        BlockHeader{.number = 2});

    TrieDbL1Source const source{*mpt_db_};
    EXPECT_EQ(source.earliest(), 0);
    auto const read = [&](uint64_t const number, bytes32_t const &key) {
        auto const value = source.read_storage(number, contract, key);
        EXPECT_TRUE(value.has_value());
        return value.has_value() ? value.value() : bytes32_t{};
    };
    // Absent account, then each block's value.
    EXPECT_EQ(read(0, slot), bytes32_t{});
    EXPECT_EQ(read(1, slot), bytes32_t{1});
    EXPECT_EQ(read(2, slot), bytes32_t{2});
    // Absent slot.
    EXPECT_EQ(read(2, bytes32_t{8}), bytes32_t{});

    auto const future = source.read_storage(3, contract, slot);
    ASSERT_TRUE(future.has_error());
    EXPECT_EQ(future.error(), mpt::DbError::version_no_longer_exist);
}

TEST_F(PrivateDomainL1Source, reads_slots_sharing_a_page)
{
    Address const contract{0xc0};
    Account const account{.nonce = 1};
    // Slots 5, 7 and 100 are in one page, slot 128 starts the next.
    ASSERT_EQ(compute_page_key(bytes32_t{5}), compute_page_key(bytes32_t{100}));
    ASSERT_NE(compute_page_key(bytes32_t{5}), compute_page_key(bytes32_t{128}));
    test::commit_sequential(
        *db_,
        StateDeltas{
            {contract,
             StateDelta{
                 .account = {std::nullopt, account},
                 .storage =
                     {{bytes32_t{5}, {bytes32_t{}, bytes32_t{0x50}}},
                      {bytes32_t{7}, {bytes32_t{}, bytes32_t{0x70}}},
                      {bytes32_t{100}, {bytes32_t{}, bytes32_t{0x64}}},
                      {bytes32_t{128}, {bytes32_t{}, bytes32_t{0x80}}}}}}},
        {},
        BlockHeader{.number = 0});
    // Rewrite one slot of the page and clear another.
    test::commit_sequential(
        *db_,
        StateDeltas{
            {contract,
             StateDelta{
                 .account = {account, account},
                 .storage =
                     {{bytes32_t{7}, {bytes32_t{0x70}, bytes32_t{0x71}}},
                      {bytes32_t{100}, {bytes32_t{0x64}, bytes32_t{}}}}}}},
        {},
        BlockHeader{.number = 1});

    TrieDbL1Source const source{*mpt_db_};
    auto const read = [&](uint64_t const number, uint64_t const slot) {
        auto const value =
            source.read_storage(number, contract, bytes32_t{slot});
        EXPECT_TRUE(value.has_value());
        return value.has_value() ? value.value() : bytes32_t{};
    };
    EXPECT_EQ(read(0, 5), bytes32_t{0x50});
    EXPECT_EQ(read(0, 7), bytes32_t{0x70});
    EXPECT_EQ(read(0, 100), bytes32_t{0x64});
    EXPECT_EQ(read(0, 128), bytes32_t{0x80});
    // Absent slots of a page that exists.
    EXPECT_EQ(read(0, 6), bytes32_t{});
    EXPECT_EQ(read(0, 129), bytes32_t{});
    // An absent page.
    EXPECT_EQ(read(0, 256), bytes32_t{});

    EXPECT_EQ(read(1, 5), bytes32_t{0x50});
    EXPECT_EQ(read(1, 7), bytes32_t{0x71});
    EXPECT_EQ(read(1, 100), bytes32_t{});
    EXPECT_EQ(read(1, 128), bytes32_t{0x80});
}

// monad-domain opens the L1 node's triedb read-only while the node writes
// it.
TEST_F(PrivateDomainL1Source, read_only_handle_follows_the_writer)
{
    Address const contract{0xc0};
    bytes32_t const slot{7};
    Account const account{.nonce = 1};
    test::commit_sequential(
        *db_,
        StateDeltas{
            {contract,
             StateDelta{
                 .account = {std::nullopt, account},
                 .storage = {{slot, {bytes32_t{}, bytes32_t{1}}}}}}},
        {},
        BlockHeader{.number = 0, .timestamp = 1'000},
        {receipt(21'000, 1)});

    mpt::AsyncIOContext io_ctx{
        mpt::ReadOnlyOnDiskDbConfig{.dbname_path = path_}};
    mpt::Db ro_db{io_ctx};
    TrieDbL1Source const source{ro_db};
    EXPECT_EQ(source.latest_finalized(), 0);
    EXPECT_EQ(source.earliest(), 0);
    {
        auto const value = source.read_storage(0, contract, slot);
        ASSERT_TRUE(value.has_value());
        EXPECT_EQ(value.value(), bytes32_t{1});
    }
    EXPECT_TRUE(source.read_finalized_header(1).has_error());

    // The writer finalizes another block.
    std::vector const receipts{receipt(21'000, 2), receipt(50'000, 3)};
    test::commit_sequential(
        *db_,
        StateDeltas{
            {contract,
             StateDelta{
                 .account = {account, account},
                 .storage = {{slot, {bytes32_t{1}, bytes32_t{2}}}}}}},
        {},
        BlockHeader{.number = 1, .timestamp = 1'001},
        receipts);
    EXPECT_EQ(source.latest_finalized(), 1);
    {
        auto const header = source.read_finalized_header(1);
        ASSERT_TRUE(header.has_value());
        EXPECT_EQ(header.value().timestamp, 1'001);
        auto const read = source.read_finalized_receipts(1);
        ASSERT_TRUE(read.has_value());
        EXPECT_EQ(read.value(), receipts);
        auto const value = source.read_storage(1, contract, slot);
        ASSERT_TRUE(value.has_value());
        EXPECT_EQ(value.value(), bytes32_t{2});
        auto const before = source.read_storage(0, contract, slot);
        ASSERT_TRUE(before.has_value());
        EXPECT_EQ(before.value(), bytes32_t{1});
    }

    // The writer's history moves past block 0.
    for (uint64_t number = 2; number <= mpt::MIN_HISTORY_LENGTH; ++number) {
        commit(number);
    }
    EXPECT_EQ(source.latest_finalized(), mpt::MIN_HISTORY_LENGTH);
    EXPECT_EQ(source.earliest(), 1);
    auto const header = source.read_finalized_header(0);
    ASSERT_TRUE(header.has_error());
    EXPECT_EQ(header.error(), mpt::DbError::version_no_longer_exist);
    auto const evicted = source.read_finalized_receipts(0);
    ASSERT_TRUE(evicted.has_error());
    EXPECT_EQ(evicted.error(), mpt::DbError::version_no_longer_exist);
    auto const storage = source.read_storage(0, contract, slot);
    ASSERT_TRUE(storage.has_error());
    EXPECT_EQ(storage.error(), mpt::DbError::version_no_longer_exist);
    {
        auto const value = source.read_storage(1, contract, slot);
        ASSERT_TRUE(value.has_value());
        EXPECT_EQ(value.value(), bytes32_t{2});
        auto const read = source.read_finalized_receipts(1);
        ASSERT_TRUE(read.has_value());
        EXPECT_EQ(read.value(), receipts);
    }
}
