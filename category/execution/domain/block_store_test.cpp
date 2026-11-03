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

#include <category/execution/domain/block_store.hpp>

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <string>
#include <unistd.h>

using namespace monad;
using namespace monad::domain;

namespace
{
    DomainBlock block(uint64_t const number)
    {
        return DomainBlock{
            .header =
                {.parent_id = number == 0
                                  ? bytes32_t{}
                                  : domain_block_id(block(number - 1).header),
                 .number = number,
                 .l1_block_number = 100 + 2 * number,
                 .l1_block_hash = bytes32_t{number + 1},
                 .timestamp = 1'000 + number},
            .transactions = {Transaction{
                .sc = {.chain_id = 0x510000004eaf},
                .nonce = number,
                .gas_limit = 21'000,
                .to = Address{0x1234}}}};
    }

    class PrivateDomainBlockStore : public ::testing::Test
    {
    protected:
        std::filesystem::path dir_;

        void SetUp() override
        {
            std::string pattern =
                (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                 "private_domain_block_store_XXXXXX")
                    .string();
            ASSERT_NE(::mkdtemp(pattern.data()), nullptr);
            dir_ = pattern;
        }

        void TearDown() override
        {
            std::filesystem::remove_all(dir_);
        }
    };
}

TEST_F(PrivateDomainBlockStore, starts_empty)
{
    DomainBlockStore const store{dir_};
    EXPECT_EQ(store.tip(), std::nullopt);
    EXPECT_EQ(store.l1_cursor(), std::nullopt);
    EXPECT_EQ(store.get(0), std::nullopt);
}

TEST_F(PrivateDomainBlockStore, reopens_at_its_tip_and_cursor)
{
    {
        DomainBlockStore store{dir_};
        for (uint64_t number = 0; number < 3; ++number) {
            store.append(block(number));
        }
        store.set_l1_cursor(107);
        EXPECT_EQ(store.tip(), block(2));
    }

    DomainBlockStore const store{dir_};
    EXPECT_EQ(store.tip(), block(2));
    EXPECT_EQ(store.l1_cursor(), 107);
    EXPECT_EQ(store.get(1), block(1));
    EXPECT_EQ(store.get(3), std::nullopt);
}

TEST_F(PrivateDomainBlockStore, finds_its_tip_across_directories)
{
    {
        DomainBlockStore store{dir_, 2};
        for (uint64_t number = 0; number < 5; ++number) {
            store.append(block(number));
        }
    }
    EXPECT_TRUE(std::filesystem::exists(dir_ / "blocks" / "2" / "4"));

    // A crash after creating a directory, before writing its first block,
    // and one in the middle of writing a block.
    std::filesystem::create_directory(dir_ / "blocks" / "3");
    std::ofstream{dir_ / "blocks" / "2" / "5.tmp"} << "partial";

    DomainBlockStore store{dir_, 2};
    EXPECT_EQ(store.tip(), block(4));
    store.append(block(5));
    EXPECT_EQ(DomainBlockStore(dir_, 2).tip(), block(5));
}
