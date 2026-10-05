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

#include "category/core/result.hpp"
#include "category/execution/ethereum/state3/state.hpp"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <span>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

class Interpreter
{
    State &state_;
    std::vector<Tensor> node_values_;
    std::span<uint8_t const> graphcode_;

    Result<void> check_magic_number();
    Result<void> check_inputs();

public:
    Interpreter(
        State &state, std::vector<Tensor> &&inputs, uint8_t const *graphcode,
        size_t graphcode_size)
        : state_(state)
        , node_values_(inputs)
        , graphcode_(graphcode, graphcode_size)
    {
    }

    Result<std::vector<Tensor>> run();

    // Allocates a tensor with uninitialized data, aligned for import into IREE
    Result<Tensor> allocate_tensor(Dtype dtype, Shape const &shape);
};

MONAD_GRAPH_EVAL_NAMESPACE_END
