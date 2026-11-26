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

// Tensors read by reference, in an account's code, for TensorRef nodes and
// code inputs

#include <category/core/result.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// Copies the elements in an account's code from `ref`'s offset on to `out`, in
// host order, from `order`. They're the size_bytes() bytes of `out`'s type,
// row-major, and the code holds no type or marker for them, so any bytes of
// any account's code can be read as a tensor of any type. InvalidTensorRef if
// they run past the end of the code. An empty tensor can be at the end of the
// code, which is offset 0 for an account with no code
Result<void>
load_code_tensor(State &, CodeRef const &ref, ByteOrder order, Tensor &out);

MONAD_GRAPH_EVAL_NAMESPACE_END
