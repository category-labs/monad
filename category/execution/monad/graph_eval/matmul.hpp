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
#include <category/execution/monad/graph_eval/tensor.hpp>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// out = x * y, for an m x k int8 matrix x and a k x n int8 matrix y, into the
// m x n int32 matrix out, all row-major. The products are exact: even 65535
// products of -128 and -128 sum to less than 2^31. Uses AVX-512 with VNNI,
// which matmul.cpp is compiled for
void matmul_i8(Tensor const &x, Tensor const &y, Tensor &out);

MONAD_GRAPH_EVAL_NAMESPACE_END
