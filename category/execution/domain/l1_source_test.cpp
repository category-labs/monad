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
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
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
                std::make_unique<OnDiskMachine>(),
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
    EXPECT_EQ(source.latest_finalized(), std::nullopt);
}

TEST_F(PrivateDomainL1Source, reads_header_hash_and_receipts)
{
    std::vector const receipts{receipt(21'000, 1), receipt(50'000, 2)};
    commit(0);
    commit(1, receipts);
    commit(2);

    TrieDbL1Source const source{*mpt_db_};
    EXPECT_EQ(source.latest_finalized(), 2);

    auto const block = source.read_finalized(1);
    ASSERT_TRUE(block.has_value());
    EXPECT_EQ(block.value().header.number, 1);
    EXPECT_EQ(block.value().header.timestamp, 1'001);
    EXPECT_EQ(
        block.value().hash,
        to_bytes(keccak256(rlp::encode_block_header(block.value().header))));
    EXPECT_EQ(block.value().receipts, receipts);

    auto const empty = source.read_finalized(2);
    ASSERT_TRUE(empty.has_value());
    EXPECT_TRUE(empty.value().receipts.empty());
}

TEST_F(PrivateDomainL1Source, fails_once_a_block_leaves_history)
{
    for (uint64_t number = 0; number <= mpt::MIN_HISTORY_LENGTH; ++number) {
        commit(number, {receipt(21'000, 1)});
    }
    ASSERT_EQ(mpt_db_->get_earliest_version(), 1);

    TrieDbL1Source const source{*mpt_db_};
    auto const expired = source.read_finalized(0);
    ASSERT_TRUE(expired.has_error());
    EXPECT_EQ(expired.error(), mpt::DbError::version_no_longer_exist);
    EXPECT_TRUE(source.read_finalized(1).has_value());
}
