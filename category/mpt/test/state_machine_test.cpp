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

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <cstddef>
#include <memory>
#include <category/core/byte_string.hpp>
#include <category/core/hex_literal.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gmock/gmock.h>

#include <cstddef>
#include <memory>
#include <set>
#include <utility>

using namespace monad::mpt;
using namespace monad;
using namespace monad::test;

namespace
{
    using DownCalls = std::set<std::pair<byte_string, unsigned char>>;
    using UpCalls = std::set<std::pair<byte_string, size_t>>;
    using ComputeCalls = std::set<byte_string>;
    using CacheCalls = std::set<byte_string>;

    struct TestStateMachine : public StateMachine
    {
        DownCalls &down_calls;
        UpCalls &up_calls;
        ComputeCalls &compute_calls;
        CacheCalls &cache_calls;
        byte_string path;

        TestStateMachine(
            DownCalls &down_calls, UpCalls &up_calls,
            ComputeCalls &compute_calls, CacheCalls &cache_calls)
            : down_calls(down_calls)
            , up_calls(up_calls)
            , compute_calls(compute_calls)
            , cache_calls(cache_calls)
        {
        }

        TestStateMachine(TestStateMachine const &) = default;

        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<TestStateMachine>(*this);
        }

        virtual void down(unsigned char nibble) override
        {
            EXPECT_LE(nibble, 0xf);
            auto const [_, success] = down_calls.emplace(path, nibble);
            EXPECT_TRUE(success);
            path.push_back(nibble);
        }

        virtual void up(size_t n) override
        {
            EXPECT_LE(n, path.size());
            // can invoke up() at same path for multiple times with async
            up_calls.emplace(path, n);
            path = path.substr(0, path.size() - n);
        }

        virtual Compute &get_compute() const override
        {
            static test::EmptyCompute compute{};
            compute_calls.emplace(path);
            return compute;
        }

        virtual bool cache() const override
        {
            cache_calls.emplace(path);
            return path.size() < 2;
        };

        virtual bool compact() const override
        {
            return false;
        }

        virtual bool is_variable_length() const override
        {
            return false;
        }
    };
}

template <typename Base>
struct StateMachineTestFixture : public Base
{
    DownCalls down_calls;
    UpCalls up_calls;
    ComputeCalls compute_calls;
    CacheCalls cache_calls;

    StateMachineTestFixture()
    {
        this->sm = std::make_unique<TestStateMachine>(
            down_calls, up_calls, compute_calls, cache_calls);

        auto const key1 = 0x1111_hex;
        auto const key2 = 0x1122_hex;

        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(key1, monad::byte_string_view{}),
            make_update(key2, monad::byte_string_view{}));
    }

    void validate_down_calls(DownCalls const &expected)
    {
        EXPECT_EQ(down_calls.size(), expected.size());
        for (auto const &e : expected) {
            EXPECT_THAT(down_calls, testing::Contains(e));
        }
    }

    void validate_up_calls(UpCalls const &expected)
    {
        EXPECT_EQ(up_calls.size(), expected.size());
        for (auto const &e : expected) {
            EXPECT_THAT(up_calls, testing::Contains(e));
        }
    }

    void validate_compute_calls(ComputeCalls const &expected)
    {
        EXPECT_EQ(compute_calls.size(), expected.size());
        for (auto const &e : expected) {
            EXPECT_THAT(compute_calls, testing::Contains(e));
        }
    }

    void validate_cache_calls(CacheCalls const &expected)
    {
        EXPECT_EQ(cache_calls.size(), expected.size());
        for (auto const &e : expected) {
            EXPECT_THAT(cache_calls, testing::Contains(e));
        }
    }
};

template <typename TFixture>
struct StateMachineTest : public TFixture
{
};

using StateMachineTestTypes = ::testing::Types<
    StateMachineTestFixture<InMemoryTrieGTest>,
    StateMachineTestFixture<OnDiskTrieGTest>>;
TYPED_TEST_SUITE(StateMachineTest, StateMachineTestTypes);

TYPED_TEST(StateMachineTest, create_new_trie)
{
    this->validate_down_calls(DownCalls{
        {{}, 1},
        {{1}, 1},
        {{1, 1}, 1},
        {{1, 1}, 2},
        {{1, 1, 1}, 1},
        {{1, 1, 2}, 2}});

    this->validate_up_calls(UpCalls{
        {{1, 1, 2, 2}, 1},
        {{1, 1, 2}, 1},
        {{1, 1}, 2},
        {{1, 1, 1, 1}, 1},
        {{1, 1, 1}, 1}});

    this->validate_compute_calls(
        ComputeCalls{{1, 1, 1, 1}, {1, 1, 2, 2}, {1, 1}});

    if (this->aux.is_on_disk()) {
        this->validate_cache_calls(
            CacheCalls{{1, 1}, {1, 1, 1, 1}, {1, 1, 2, 2}});
    }
}

TYPED_TEST(StateMachineTest, modify_existing)
{
    this->down_calls.clear();
    this->up_calls.clear();
    this->compute_calls.clear();
    this->cache_calls.clear();

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(0x1122_hex, monad::byte_string_view{}));

    this->validate_down_calls(
        DownCalls{{{}, {1}}, {{1}, 1}, {{1, 1}, 2}, {{1, 1, 2}, 2}});

    this->validate_up_calls(
        UpCalls{{{1, 1, 2, 2}, 1}, {{1, 1, 2}, 1}, {{1, 1}, 2}});

    this->validate_compute_calls(ComputeCalls{{1, 1, 2, 2}, {1, 1}});

    if (this->aux.is_on_disk()) {
        this->validate_cache_calls(CacheCalls{{1, 1}, {1, 1, 2, 2}});
    }
}

TYPED_TEST(StateMachineTest, mismatch)
{
    this->down_calls.clear();
    this->up_calls.clear();
    this->compute_calls.clear();
    this->cache_calls.clear();

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(0x1222_hex, monad::byte_string_view{}));

    this->validate_down_calls(
        DownCalls{{{}, {1}}, {{1}, 2}, {{1, 2}, 2}, {{1, 2, 2}, 2}, {{1}, 1}});

    this->validate_up_calls(
        UpCalls{{{1, 2, 2, 2}, 2}, {{1, 2}, 1}, {{1}, 1}, {{1, 1}, 1}});

    this->validate_compute_calls(ComputeCalls{{1}, {1, 1}, {1, 2, 2, 2}});

    if (this->aux.is_on_disk()) {
        this->validate_cache_calls(CacheCalls{{1}, {1, 1}, {1, 2, 2, 2}});
    }
}

TYPED_TEST(StateMachineTest, mismatch_with_extension)
{
    this->down_calls.clear();
    this->up_calls.clear();
    this->compute_calls.clear();
    this->cache_calls.clear();

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(0x2222_hex, monad::byte_string_view{}));

    this->validate_down_calls(DownCalls{
        {{}, {2}}, {{2}, 2}, {{2, 2}, 2}, {{2, 2, 2}, 2}, {{}, 1}, {{1}, 1}});

    this->validate_up_calls(UpCalls{{{1, 1}, 2}, {{2, 2, 2, 2}, 3}, {{2}, 1}});

    this->validate_compute_calls(ComputeCalls{{}, {1, 1}, {2, 2, 2, 2}});

    if (this->aux.is_on_disk()) {
        this->validate_cache_calls(CacheCalls{{}, {1, 1}, {2, 2, 2, 2}});
    }
}

TYPED_TEST(StateMachineTest, add_to_branch)
{
    this->down_calls.clear();
    this->up_calls.clear();
    this->compute_calls.clear();
    this->cache_calls.clear();

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(0x1133_hex, monad::byte_string_view{}));

    this->validate_down_calls(
        DownCalls{{{}, 1}, {{1}, 1}, {{1, 1}, 3}, {{1, 1, 3}, 3}});

    this->validate_up_calls(
        UpCalls{{{1, 1, 3, 3}, 1}, {{1, 1, 3}, 1}, {{1, 1}, 2}});

    this->validate_compute_calls(ComputeCalls{{1, 1}, {1, 1, 3, 3}});

    if (this->aux.is_on_disk()) {
        this->validate_cache_calls(CacheCalls{{1, 1}, {1, 1, 3, 3}});
    }
}
