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

#include "category/execution/monad/graph_eval/tensor.hpp"
#include <category/core/result.hpp>
#include <category/execution/monad/graph_eval/config.hpp>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

class Kernel
{
    const char *kernel_name_;
public:
    void operator()(std::vector<Tensor> &inputs, Tensor &output) const;
    explicit constexpr Kernel(const char* kernel_name) : kernel_name_(kernel_name) {};
};

MONAD_GRAPH_EVAL_NAMESPACE_END
