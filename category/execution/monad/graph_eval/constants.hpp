// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/execution/monad/graph_eval/config.hpp>

#include <cstddef>
#include <cstdint>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

constexpr uint64_t IREE_ALIGNMENT = 64;

// Memory for the tensors a graph evaluation computes; an evaluation that needs
// more fails with OutOfMemory
constexpr uint64_t ARENA_SIZE = uint64_t{64} * 1024 * 1024;

constexpr std::size_t MAX_GRAPH_INPUTS = 8;
constexpr std::size_t MAX_GRAPH_OUTPUTS = 8;

MONAD_GRAPH_EVAL_NAMESPACE_END
