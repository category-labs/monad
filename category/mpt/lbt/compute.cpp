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

#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/lbt/compute.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <array>
#include <cstddef>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

namespace lbt
{
    Commitment commit_children(Node const &node)
    {
        std::array<Entry, 16> entries;
        size_t n = 0;
        for (auto const [index, branch] : NodeChildrenRange(node.mask)) {
            entries[n++] = Entry{
                .index = branch,
                .child = Commitment::from_child_data(
                    node.child_data_view(index),
                    ((node.child_value_mask >> branch) & 1u) != 0)};
        }
        return branch_commit<4>(std::span{entries}.first(n));
    }

    Commitment commit_children(std::span<ChildData const> const children)
    {
        std::array<Entry, 16> entries;
        size_t n = 0;
        for (auto const &child : children) {
            if (!child.is_valid()) {
                continue;
            }
            entries[n++] = Entry{
                .index = child.branch,
                .child = Commitment::from_child_data(
                    {child.data, child.len}, child.has_value)};
        }
        return branch_commit<4>(std::span{entries}.first(n));
    }

    NibblesView full_leaf_key(
        NibblesView const prefix, NibblesView const path, Nibbles &storage)
    {
        MONAD_ASSERT(
            path.nibble_size() <= KEY_NIBBLES &&
            prefix.nibble_size() <= KEY_NIBBLES);
        unsigned const above = KEY_NIBBLES - path.nibble_size();
        MONAD_ASSERT(prefix.nibble_size() >= above);
        MONAD_ASSERT(path.starts_with(prefix.substr(above)));
        if (prefix.nibble_size() == KEY_NIBBLES) {
            return prefix;
        }
        if (above == 0) {
            return path;
        }
        storage = concat(prefix.substr(0, above), path);
        return storage;
    }
}

MONAD_MPT_NAMESPACE_END
