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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

MONAD_NAMESPACE_BEGIN

class CodeTraceRunner
{
public:
    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    Map<bytes32_t, vm::SharedIntercode> codes{};

    bool operator()(trace::state_trace::ReadCode const &op);
};

MONAD_NAMESPACE_END
