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

#pragma once

#include <category/mpt/db.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

namespace monad::test
{
    // Counts children whose bit in their parent's child_value_mask disagrees
    // with whether the child has a value.
    struct ChildValueMaskChecker final : public mpt::TraverseMachine
    {
        std::vector<uint16_t> parent_masks;
        size_t children_checked{0};
        size_t mismatches{0};

        virtual bool
        down(unsigned char const branch, mpt::Node const &node) override
        {
            if (branch != mpt::INVALID_BRANCH) {
                bool const bit = ((parent_masks.back() >> branch) & 1) != 0;
                mismatches += bit != node.has_value() ? 1 : 0;
                ++children_checked;
            }
            parent_masks.push_back(node.child_value_mask);
            return true;
        }

        virtual void up(unsigned char, mpt::Node const &) override
        {
            parent_masks.pop_back();
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<ChildValueMaskChecker>(*this);
        }
    };

    inline void expect_child_value_masks(
        mpt::Db &db, mpt::Node::SharedPtr const &root, uint64_t const version)
    {
        ChildValueMaskChecker checker;
        ASSERT_TRUE(
            db.traverse_blocking(mpt::NodeCursor{root}, checker, version));
        EXPECT_GT(checker.children_checked, 0u);
        EXPECT_EQ(checker.mismatches, 0u);
    }
}
