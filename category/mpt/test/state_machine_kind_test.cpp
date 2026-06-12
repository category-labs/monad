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

#include <category/mpt/compute.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdlib>
#include <memory>

using namespace monad::mpt;

namespace
{
    // Stand-in StateMachine that records which factory invocation produced
    // it. Tests use this in place of a real OnDiskMachine so the registry
    // test stays inside the mpt module — production SMs live in execution/.
    struct FakeStateMachine final : public StateMachine
    {
        explicit FakeStateMachine(int const tag)
            : tag_(tag)
        {
        }

        std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<FakeStateMachine>(tag_);
        }

        void down(unsigned char) override {}

        void up(size_t) override {}

        Compute &get_compute() const override
        {
            std::abort(); // not exercised
        }

        bool cache() const override
        {
            return false;
        }

        bool compact() const override
        {
            return false;
        }

        bool is_variable_length() const override
        {
            return false;
        }

        int tag_;
    };
}

TEST(state_machine_kind, register_then_create_returns_factory_output)
{
    register_state_machine(state_machine_kind::ethereum, [] {
        return std::unique_ptr<StateMachine>(new FakeStateMachine{42});
    });
    auto const sm = create_state_machine(state_machine_kind::ethereum);
    ASSERT_NE(sm, nullptr);
    auto *const fake = dynamic_cast<FakeStateMachine *>(sm.get());
    ASSERT_NE(fake, nullptr);
    EXPECT_EQ(fake->tag_, 42);
}

TEST(state_machine_kind, re_register_overwrites)
{
    register_state_machine(state_machine_kind::ethereum, [] {
        return std::unique_ptr<StateMachine>(new FakeStateMachine{1});
    });
    register_state_machine(state_machine_kind::ethereum, [] {
        return std::unique_ptr<StateMachine>(new FakeStateMachine{2});
    });
    auto const sm = create_state_machine(state_machine_kind::ethereum);
    auto *const fake = dynamic_cast<FakeStateMachine *>(sm.get());
    ASSERT_NE(fake, nullptr);
    EXPECT_EQ(fake->tag_, 2);
}

TEST(state_machine_kind, create_unregistered_aborts)
{
    // An in-range kind with no registered factory aborts. Use the top slot
    // so it stays unregistered as real kinds are added at the bottom.
    EXPECT_DEATH(
        (void)create_state_machine(
            static_cast<state_machine_kind>(NUM_STATE_MACHINE_KINDS - 1)),
        "");
}
