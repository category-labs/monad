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

#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <cstdint>
#include <span>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

struct TensorAllocationRecord
{
    uint64_t offset;
    TensorType type;
};

class Graphcode
{
public:
    explicit Graphcode(std::span<uint8_t const> const);

    constexpr uint8_t const *code() const noexcept
    {
        return code_;
    }

    constexpr size_t code_size() const noexcept
    {
        return code_size_;
    }

    constexpr size_t arena_size() const noexcept
    {
        return arena_size_;
    }

    constexpr GraphEvalError validation_result() const noexcept
    {
        return validation_result_;
    }

    constexpr std::vector<TensorAllocationRecord> const &
    tensor_allocation_records() const noexcept
    {
        return tensor_allocation_records_;
    }

    constexpr std::span<uint8_t const> code_span() const noexcept
    {
        return {code(), code_size()};
    }

private:
    uint8_t const *code_;
    size_t code_size_;
    size_t arena_size_ = 0;
    GraphEvalError validation_result_ = GraphEvalError::Success;
    std::vector<TensorAllocationRecord> tensor_allocation_records_;

    Result<void> compute_tensor_allocations();
};

MONAD_GRAPH_EVAL_NAMESPACE_END
