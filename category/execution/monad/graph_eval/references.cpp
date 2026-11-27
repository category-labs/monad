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
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/vm/code.hpp>
#include <category/vm/interpreter/intercode.hpp>

#include <cstddef>
#include <cstdint>
#include <span>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void> load_code_tensor(State &state, CodeRef const &ref, Tensor &out)
{
    vm::SharedVarcode const varcode = state.get_code(ref.address);
    std::span<uint8_t const> const code = varcode->intercode()->code_span();
    size_t const size = out.type().size_bytes();
    // The offset is checked first, so that the subtraction can't wrap
    if (ref.offset > code.size() || size > code.size() - ref.offset) {
        return GraphEvalError::InvalidTensorRef;
    }
    copy_elements(
        out.type().dtype(),
        ByteOrder::LittleEndian,
        code.subspan(ref.offset, size),
        out.data());
    return outcome::success();
}

MONAD_GRAPH_EVAL_NAMESPACE_END
