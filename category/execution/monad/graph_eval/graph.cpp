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

#include <category/core/result.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>

#include <cstddef>
#include <cstdint>
#include <span>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<std::span<uint8_t const>>
read_bytes(std::span<uint8_t const> &input, uint64_t const size)
{
    if (input.size() < size) {
        return GraphEvalError::GraphValidationError;
    }
    auto const bytes = input.first(static_cast<size_t>(size));
    input = input.subspan(static_cast<size_t>(size));
    return bytes;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
