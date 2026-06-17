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

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/state3/page_tracker.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

using namespace monad;

namespace
{
    constexpr bytes32_t SLOT_A{0x1ea0};
    constexpr bytes32_t SLOT_A2{0x1eaf};
    constexpr bytes32_t SLOT_B{0xdeadbeef};
}

TEST(PageTracker, cold_write)
{
    PageTracker pt;

    EXPECT_TRUE(pt.update_page(SLOT_A, EVMC_STORAGE_ADDED).first_page_write);
    EXPECT_FALSE(
        pt.update_page(SLOT_A2, EVMC_STORAGE_MODIFIED).first_page_write);
    EXPECT_FALSE(pt.update_page(SLOT_A, EVMC_STORAGE_DELETED).first_page_write);
}

TEST(PageTracker, state_growth)
{
    PageTracker pt;

    EXPECT_TRUE(pt.update_page(SLOT_A, EVMC_STORAGE_ADDED).grew_state);
    EXPECT_TRUE(pt.update_page(SLOT_A2, EVMC_STORAGE_ADDED).grew_state);
    EXPECT_FALSE(pt.update_page(SLOT_A, EVMC_STORAGE_MODIFIED).grew_state);
}

TEST(PageTracker, intra_txn_free)
{
    PageTracker pt;

    EXPECT_TRUE(pt.update_page(SLOT_A, EVMC_STORAGE_ADDED).grew_state);
    EXPECT_TRUE(pt.update_page(SLOT_A2, EVMC_STORAGE_ADDED).grew_state);
    EXPECT_FALSE(pt.update_page(SLOT_A, EVMC_STORAGE_DELETED).grew_state);
    EXPECT_FALSE(pt.update_page(SLOT_A, EVMC_STORAGE_DELETED_ADDED).grew_state);
}

TEST(PageTracker, distinct_pages)
{
    PageTracker pt;

    EXPECT_TRUE(pt.update_page(SLOT_A, EVMC_STORAGE_ADDED).first_page_write);
    EXPECT_FALSE(pt.update_page(SLOT_A2, EVMC_STORAGE_ADDED).first_page_write);

    auto const r = pt.update_page(SLOT_B, EVMC_STORAGE_ADDED);
    EXPECT_TRUE(r.first_page_write);
    EXPECT_TRUE(r.grew_state);
}

TEST(PageTracker, cold_read_then_warm_read)
{
    PageTracker pt;

    EXPECT_EQ(pt.access_page(SLOT_A), EVMC_ACCESS_COLD);
    EXPECT_EQ(pt.access_page(SLOT_A2), EVMC_ACCESS_WARM);
    EXPECT_EQ(pt.access_page(SLOT_B), EVMC_ACCESS_COLD);
    EXPECT_EQ(pt.access_page(SLOT_B), EVMC_ACCESS_WARM);
}

TEST(PageTracker, deleted_then_readded_returns_to_baseline)
{
    PageTracker pt;
    pt.update_page(SLOT_A, EVMC_STORAGE_DELETED);
    pt.update_page(SLOT_A, EVMC_STORAGE_DELETED_ADDED);
    EXPECT_TRUE(pt.update_page(SLOT_A2, EVMC_STORAGE_ADDED).grew_state);
}

TEST(PageTracker, deleted_then_restored_returns_to_baseline)
{
    PageTracker pt;
    pt.update_page(SLOT_A, EVMC_STORAGE_DELETED);
    pt.update_page(SLOT_A, EVMC_STORAGE_DELETED_RESTORED);
    EXPECT_TRUE(pt.update_page(SLOT_A2, EVMC_STORAGE_ADDED).grew_state);
}
