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
#include <category/execution/ethereum/state3/version_stack.hpp>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <random>
#include <string>
#include <utility>

using monad::VersionStack;

namespace
{
    template <class T>
    class DequeVersionStack
    {
        std::deque<std::pair<unsigned, T>> stack_;

    public:
        explicit DequeVersionStack(T value, unsigned version = 0)
        {
            stack_.emplace_back(version, std::move(value));
        }

        size_t size() const
        {
            return stack_.size();
        }

        unsigned version() const
        {
            return stack_.back().first;
        }

        T const &recent() const
        {
            return stack_.back().second;
        }

        T &recent()
        {
            return stack_.back().second;
        }

        T &current(unsigned version)
        {
            if (version > stack_.back().first) {
                T value = stack_.back().second;
                stack_.emplace_back(version, std::move(value));
            }
            return stack_.back().second;
        }

        void pop_accept(unsigned version)
        {
            auto const size = stack_.size();
            if (version == stack_.back().first) {
                if (size > 1 &&
                    stack_[size - 2].first + 1 == stack_[size - 1].first) {
                    stack_[size - 2].second =
                        std::move(stack_[size - 1].second);
                    stack_.pop_back();
                }
                else {
                    stack_.back().first = version - 1;
                }
            }
        }

        bool pop_reject(unsigned version)
        {
            if (version == stack_.back().first) {
                stack_.pop_back();
            }
            return stack_.empty();
        }
    };

    struct AccountLike
    {
        std::array<std::uint64_t, 16> words{};
        std::shared_ptr<std::string> shared{
            std::make_shared<std::string>("state")};
    };

    struct LifetimeValue
    {
        static inline int alive = 0;
        int value{};

        explicit LifetimeValue(int v = 0)
            : value{v}
        {
            ++alive;
        }

        LifetimeValue(LifetimeValue const &other)
            : value{other.value}
        {
            ++alive;
        }

        LifetimeValue(LifetimeValue &&other) noexcept
            : value{other.value}
        {
            ++alive;
        }

        LifetimeValue &operator=(LifetimeValue const &) = default;
        LifetimeValue &operator=(LifetimeValue &&) noexcept = default;

        ~LifetimeValue()
        {
            --alive;
        }
    };

    void mutate_account_state(monad::AccountState &state, uint64_t seed)
    {
        monad::bytes32_t const key{seed % 13 + 1};
        monad::bytes32_t const value{seed * 19 + 7};
        state.storage_ = std::move(state.storage_).insert({key, value});
        state.set_transient_storage(key, value);
        state.access_storage(key);
        state.page_tracker_.access_page(key);
        if ((seed & 1U) != 0) {
            state.touch();
        }
        if ((seed & 7U) == 0) {
            state.destruct();
        }
    }

    // Holding a copy keeps every immer node shared, so the oracle always takes
    // the copying path and can detect an in-place update that leaks into
    // another snapshot.
    void mutate_account_state_without_in_place_updates(
        monad::AccountState &state, uint64_t const seed)
    {
        monad::AccountState const pinned = state;
        mutate_account_state(state, seed);
    }

    void expect_same_state(
        monad::AccountState const &actual, monad::AccountState const &expected)
    {
        EXPECT_EQ(actual.storage_.size(), expected.storage_.size());
        EXPECT_EQ(
            actual.transient_storage_.size(),
            expected.transient_storage_.size());
        EXPECT_EQ(actual.is_touched(), expected.is_touched());
        EXPECT_EQ(actual.is_destructed(), expected.is_destructed());
        for (uint64_t key_number = 1; key_number <= 13; ++key_number) {
            monad::bytes32_t const key{key_number};
            auto const *a = actual.storage_.find(key);
            auto const *b = expected.storage_.find(key);
            ASSERT_EQ(a != nullptr, b != nullptr);
            if (a) {
                EXPECT_EQ(*a, *b);
            }
            EXPECT_EQ(
                actual.get_transient_storage(key),
                expected.get_transient_storage(key));
            EXPECT_EQ(
                actual.get_accessed_storage().count(key),
                expected.get_accessed_storage().count(key));
        }
    }
}

TEST(VersionStack, MatchesDequeAcrossNestedAndSparseFrameTransitions)
{
    VersionStack<int> actual{10};
    DequeVersionStack<int> expected{10};

    auto compare = [&] {
        ASSERT_EQ(actual.size(), expected.size());
        if (actual.size()) {
            EXPECT_EQ(actual.version(), expected.version());
            EXPECT_EQ(actual.recent(), expected.recent());
        }
    };

    actual.current(1) = expected.current(1) = 11;
    actual.current(2) = expected.current(2) = 12;
    actual.pop_accept(2);
    expected.pop_accept(2);
    compare();
    actual.pop_reject(1);
    expected.pop_reject(1);
    compare();

    VersionStack<int> sparse{10, 0};
    DequeVersionStack<int> sparse_expected{10, 0};
    sparse.current(7) = sparse_expected.current(7) = 17;
    sparse.pop_accept(7);
    sparse_expected.pop_accept(7);
    EXPECT_EQ(sparse.version(), 6);
    EXPECT_FALSE(sparse.pop_reject(5));
    EXPECT_FALSE(sparse_expected.pop_reject(5));
    EXPECT_FALSE(sparse.pop_reject(6));
    EXPECT_FALSE(sparse_expected.pop_reject(6));
    EXPECT_EQ(sparse.size(), sparse_expected.size());

    VersionStack<int> new_in_frame{29, 4};
    EXPECT_TRUE(new_in_frame.pop_reject(4));
    EXPECT_FALSE(VersionStack<int>{3}.pop_reject(1));
}

TEST(VersionStack, RandomizedAccountStateHistoryMatchesDeque)
{
    constexpr uint32_t seed = 0x51A7E;
    std::mt19937 random{seed};
    // Like State::current_, the stack exists only while the account has
    // history, and it is created at the frame that first touches the account.
    std::optional<VersionStack<monad::AccountState>> actual;
    std::optional<DequeVersionStack<monad::AccountState>> expected;
    unsigned frame = 0;
    unsigned nested_creations = 0;
    unsigned rejected_to_empty = 0;

    for (unsigned step = 0; step < 5000; ++step) {
        unsigned const op = static_cast<unsigned>(random() % 10);
        if (op < 4) {
            if (!actual.has_value()) {
                actual.emplace(
                    monad::AccountState{std::optional<monad::Account>{}},
                    frame);
                expected.emplace(
                    monad::AccountState{std::optional<monad::Account>{}},
                    frame);
                if (frame != 0) {
                    ++nested_creations;
                }
            }
            auto &a = actual->current(frame);
            auto &e = expected->current(frame);
            uint64_t const mutation = random();
            mutate_account_state(a, mutation);
            mutate_account_state_without_in_place_updates(e, mutation);
        }
        else if (frame == 0) {
            if (op == 9) {
                // The transaction ends, and the next one starts without
                // history for the account.
                actual.reset();
                expected.reset();
            }
            else {
                ++frame;
            }
        }
        else if (op < 6 && frame < 18) {
            ++frame;
        }
        else if (op < 8) {
            if (actual.has_value()) {
                actual->pop_accept(frame);
                expected->pop_accept(frame);
            }
            --frame;
        }
        else {
            if (actual.has_value()) {
                bool const actual_empty = actual->pop_reject(frame);
                bool const expected_empty = expected->pop_reject(frame);
                ASSERT_EQ(actual_empty, expected_empty)
                    << "seed=" << seed << " step=" << step;
                if (actual_empty) {
                    // State::pop_reject erases accounts whose stacks are empty.
                    actual.reset();
                    expected.reset();
                    ++rejected_to_empty;
                }
            }
            --frame;
        }

        ASSERT_EQ(actual.has_value(), expected.has_value())
            << "seed=" << seed << " step=" << step;
        if (actual.has_value()) {
            ASSERT_EQ(actual->size(), expected->size())
                << "seed=" << seed << " step=" << step;
            ASSERT_EQ(actual->version(), expected->version())
                << "seed=" << seed << " step=" << step;
            expect_same_state(actual->recent(), expected->recent());
        }
    }

    EXPECT_GT(nested_creations, 0);
    EXPECT_GT(rejected_to_empty, 0);
}

TEST(VersionStack, RootAndOverflowReferencesSurviveOwnerMovesAndMapErase)
{
    VersionStack<AccountLike> source{AccountLike{}};
    AccountLike *const root = &source.recent();
    root->words[0] = 10;
    AccountLike *const overflow_one = &source.current(1);
    overflow_one->words[1] = 11;
    AccountLike *const overflow_two = &source.current(2);
    overflow_two->words[2] = 12;

    VersionStack<AccountLike> moved{std::move(source)};
    EXPECT_EQ(&moved.current(2), overflow_two);
    EXPECT_EQ(root->words[0], 10);
    EXPECT_EQ(overflow_one->words[1], 11);
    EXPECT_EQ(overflow_two->words[2], 12);
    EXPECT_NE(root, overflow_one);

    using Owners =
        ankerl::unordered_dense::segmented_map<int, VersionStack<AccountLike>>;
    Owners owners;
    owners.try_emplace(1, AccountLike{});
    owners.try_emplace(2, AccountLike{});
    auto it = owners.find(2);
    AccountLike *const map_root = &it->second.recent();
    map_root->words[0] = 20;
    AccountLike *const map_overflow = &it->second.current(1);
    map_overflow->words[1] = 21;
    auto erase_it = owners.find(1);
    owners.erase(erase_it);
    it = owners.find(2);
    ASSERT_NE(it, owners.end());
    EXPECT_EQ(&it->second.recent(), map_overflow);
    EXPECT_EQ(map_root->words[0], 20);
    EXPECT_EQ(map_overflow->words[1], 21);
    EXPECT_NE(map_root, map_overflow);
}

TEST(VersionStack, HandlesDeepStacksAndIterativeDestruction)
{
    LifetimeValue::alive = 0;
    {
        VersionStack<LifetimeValue> stack{LifetimeValue{0}};
        for (unsigned i = 1; i < 100000; ++i) {
            stack.current(i).value = static_cast<int>(i);
        }
        EXPECT_EQ(stack.size(), 100000);
        EXPECT_EQ(stack.recent().value, 99999);
    }
    EXPECT_EQ(LifetimeValue::alive, 0);
}

TEST(VersionStack, MoveAssignmentReleasesOldChainAndTransfersOwnership)
{
    LifetimeValue::alive = 0;
    {
        VersionStack<LifetimeValue> source{LifetimeValue{7}};
        source.current(1).value = 8;
        VersionStack<LifetimeValue> destination{LifetimeValue{1}};
        destination.current(1).value = 2;
        destination.current(2).value = 3;
        EXPECT_EQ(LifetimeValue::alive, 5);
        destination = std::move(source);
        EXPECT_EQ(LifetimeValue::alive, 2);
        EXPECT_EQ(destination.size(), 2);
        EXPECT_EQ(destination.recent().value, 8);
    }
    EXPECT_EQ(LifetimeValue::alive, 0);
}
