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

#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/page_tracker.hpp>

#include <gtest/gtest.h>
#include <immer/vector.hpp>

#include <optional>
#include <utility>

TEST(OwnedStateUpdates, RetainedAccountSnapshotsRemainPersistent)
{
    monad::AccountState original{std::optional<monad::Account>{}};
    monad::bytes32_t const key_one{1};
    monad::bytes32_t const key_two{128};
    monad::bytes32_t const value_one{101};
    monad::bytes32_t const value_two{202};

    original.storage_ =
        std::move(original.storage_).insert({key_one, value_one});
    original.set_transient_storage(key_one, value_one);
    EXPECT_EQ(original.access_storage(key_one), MONAD_ACCESS_COLD);
    EXPECT_EQ(original.page_tracker_.access_page(key_one), MONAD_ACCESS_COLD);

    monad::AccountState frame = original;
    auto const retained_storage = original.storage_;
    auto const retained_transient = original.transient_storage_;
    auto const retained_warmth = original.get_accessed_storage();
    auto retained_pages = original.page_tracker_;

    frame.storage_ = std::move(frame.storage_).insert({key_two, value_two});
    frame.set_transient_storage(key_two, value_two);
    EXPECT_EQ(frame.access_storage(key_two), MONAD_ACCESS_COLD);
    EXPECT_EQ(frame.page_tracker_.access_page(key_two), MONAD_ACCESS_COLD);

    ASSERT_EQ(retained_storage.size(), 1);
    EXPECT_EQ(*retained_storage.find(key_one), value_one);
    EXPECT_EQ(retained_storage.find(key_two), nullptr);
    EXPECT_EQ(retained_transient.size(), 1);
    EXPECT_EQ(*retained_transient.find(key_one), value_one);
    EXPECT_EQ(retained_transient.find(key_two), nullptr);
    EXPECT_EQ(retained_warmth.count(key_one), 1);
    EXPECT_EQ(retained_warmth.count(key_two), 0);
    EXPECT_EQ(retained_pages.access_page(key_two), MONAD_ACCESS_COLD);
    EXPECT_EQ(frame.page_tracker_.access_page(key_two), MONAD_ACCESS_WARM);

    // Retained snapshots continue to protect their nodes during later updates.
    monad::bytes32_t const value_three{303};
    frame.storage_ = std::move(frame.storage_).insert({key_one, value_three});
    frame.storage_ = std::move(frame.storage_).insert({key_two, value_three});
    frame.set_transient_storage(key_one, value_three);
    frame.set_transient_storage(key_two, value_three);
    EXPECT_EQ(*frame.storage_.find(key_one), value_three);
    EXPECT_EQ(*frame.storage_.find(key_two), value_three);
    EXPECT_EQ(frame.get_transient_storage(key_one), value_three);
    EXPECT_EQ(frame.get_transient_storage(key_two), value_three);

    ASSERT_EQ(retained_storage.size(), 1);
    EXPECT_EQ(*retained_storage.find(key_one), value_one);
    EXPECT_EQ(retained_storage.find(key_two), nullptr);
    ASSERT_EQ(retained_transient.size(), 1);
    EXPECT_EQ(*retained_transient.find(key_one), value_one);
    EXPECT_EQ(retained_transient.find(key_two), nullptr);
    EXPECT_EQ(*original.storage_.find(key_one), value_one);
    EXPECT_EQ(original.get_transient_storage(key_one), value_one);
}

TEST(OwnedStateUpdates, ImmerDocumentsSelfMoveAssignmentForRvalueUpdates)
{
    using Map = monad::AccountState::StorageMap;
    Map storage;
    monad::bytes32_t const key{3};
    monad::bytes32_t const value{303};
    storage = std::move(storage).insert({key, value});
    EXPECT_EQ(*storage.find(key), value);

    immer::vector<int> logs;
    logs = std::move(logs).push_back(7);
    logs = std::move(logs).push_back(11);
    ASSERT_EQ(logs.size(), 2);
    EXPECT_EQ(logs[0], 7);
    EXPECT_EQ(logs[1], 11);
}
