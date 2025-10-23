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

#pragma once
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>

#include <cstdint>
#include <memory>

MONAD_MPT_NAMESPACE_BEGIN

struct NodeCursor
{
    std::shared_ptr<Node> node{nullptr};
    unsigned prefix_index{0};

    constexpr NodeCursor()
        : node{nullptr}
        , prefix_index{0}
    {
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NodeCursor(
        std::shared_ptr<Node> node_, unsigned prefix_index_ = 0)
        : node{std::move(node_)}
        , prefix_index{prefix_index_}
    {
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }
};

static_assert(sizeof(NodeCursor) == 24);
static_assert(alignof(NodeCursor) == 8);

MONAD_MPT_NAMESPACE_END
