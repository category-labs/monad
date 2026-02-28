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

#include <category/core/byte_string.hpp>
#include <category/core/likely.h>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>

MONAD_MPT_NAMESPACE_BEGIN

using TraverseCallback = std::function<void(NibblesView, byte_string_view)>;

class RangedGetMachine : public TraverseMachine
{
    Nibbles path_;
    Nibbles const min_;
    Nibbles const max_;
    TraverseCallback callback_;

private:
    // Check if any descendant of path could fall within [min, max). When
    // path is shorter than min, compare path against the truncated min
    // prefix: e.g. range [0x0124, 0x1234) at path 0x1 should continue
    // because descendants like 0x1000 are in range (0x1 >= 0x0).
    bool does_key_intersect_with_range(NibblesView const path)
    {
        auto const prefix_len =
            std::min(path.nibble_size(), NibblesView{min_}.nibble_size());
        auto const min_prefix = NibblesView{min_}.substr(0, prefix_len);
        return path >= min_prefix && path < NibblesView{max_};
    }

public:
    RangedGetMachine(
        NibblesView const min, NibblesView const max, TraverseCallback callback)
        : path_{}
        , min_{min}
        , max_{max}
        , callback_(std::move(callback))
    {
    }

    virtual bool down(unsigned char const branch, Node const &node) override
    {
        if (MONAD_UNLIKELY(branch == INVALID_BRANCH)) {
            return true;
        }

        Nibbles next_path =
            concat(NibblesView{path_}, branch, node.path_nibble_view());
        if (!does_key_intersect_with_range(next_path)) {
            return false;
        }

        path_ = std::move(next_path);
        if (node.has_value() && path_ >= NibblesView{min_}) {
            callback_(path_, node.value());
        }

        return true;
    }

    void up(unsigned char const branch, Node const &node) override
    {
        auto const path_view = NibblesView{path_};
        unsigned const rem_size = [&] {
            if (branch == INVALID_BRANCH) {
                return 0u;
            }
            constexpr unsigned BRANCH_SIZE = 1;
            return path_view.nibble_size() - BRANCH_SIZE -
                   node.path_nibble_view().nibble_size();
        }();
        path_ = path_view.substr(0, rem_size);
    }

    bool should_visit(Node const &, unsigned char const branch) override
    {
        auto const child = concat(NibblesView{path_}, branch);
        return does_key_intersect_with_range(child);
    }

    std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<RangedGetMachine>(*this);
    }
};

class GetAllMachine : public TraverseMachine
{
    Nibbles path_;
    TraverseCallback callback_;

public:
    explicit GetAllMachine(TraverseCallback callback)
        : path_()
        , callback_(std::move(callback))
    {
    }

    GetAllMachine(GetAllMachine const &other) = default;

    virtual bool down(unsigned char const branch, Node const &node) override
    {
        if (MONAD_UNLIKELY(branch == INVALID_BRANCH)) {
            MONAD_ASSERT(path_.nibble_size() == 0);
            return true;
        }

        path_ = concat(NibblesView{path_}, branch, node.path_nibble_view());
        if (node.has_value()) {
            callback_(path_, node.value());
        }
        return true;
    }

    virtual void up(unsigned char const branch, Node const &node) override
    {
        auto const path_view = NibblesView{path_};
        unsigned const prefix_size =
            branch == INVALID_BRANCH
                ? 0
                : path_view.nibble_size() - node.path_nibbles_len() - 1;
        path_ = path_view.substr(0, prefix_size);
    }

    virtual std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<GetAllMachine>(*this);
    }
};

MONAD_MPT_NAMESPACE_END
