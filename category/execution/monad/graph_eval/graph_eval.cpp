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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>
#include <category/execution/monad/graph_eval/kernel.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>

#include <iree/hal/allocator.h>
#include <iree/hal/buffer.h>
#include <iree/hal/buffer_view.h>
#include <iree/runtime/api.h>
#include <iree/vm/bytecode/module.h>

#include <boost/outcome/try.hpp>

#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iree/runtime/session.h>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

//
// Function Selectors
//

struct PrecompileSelector
{
    static constexpr uint32_t EVAL_OP =
        abi_encode_selector("evalOp(uint16,(uint8,uint16[],bytes)[])");

    static constexpr uint32_t EVAL_GRAPH =
        abi_encode_selector("evalGraph(address,(uint8,uint16[],bytes)[])");
};

//
// Gas costs (dummy)
//

constexpr uint64_t EVAL_OP_COST = 100;
constexpr uint64_t EVAL_GRAPH_COST = 100;
constexpr uint64_t FALLBACK_COST = 100;

//
// Limits
//

constexpr uint64_t MAX_INPUTS = 16;

// Tensor is a dynamic type, so a Tensor[] tail is its length, then the offset
// of each element from the end of the length word, then the elements. The
// elements are read in place, so only the canonical layout is accepted, as for
// the tuples inside them: each element right after the one before, the first
// right after the offsets.
Result<std::vector<Tensor>>
abi_decode_dynamic_tensor_array_tail(byte_string_view &input)
{
    BOOST_OUTCOME_TRY(auto const n_inputs_be, abi_decode_fixed<u256_be>(input));
    auto const n_inputs_256 = n_inputs_be.native();
    if (n_inputs_256.as_words()[1] || n_inputs_256.as_words()[2] ||
        n_inputs_256.as_words()[3]) {
        return GraphEvalError::InvalidInput;
    }
    auto const n_inputs = n_inputs_256.as_words()[0];
    if (n_inputs > MAX_INPUTS) {
        return GraphEvalError::ArityError;
    }

    byte_string_view const elements = input;
    std::array<u256_be, MAX_INPUTS> offsets{};
    for (size_t i = 0; i < n_inputs; i++) {
        BOOST_OUTCOME_TRY(offsets[i], abi_decode_fixed<u256_be>(input));
    }

    std::vector<Tensor> inputs;
    inputs.reserve(n_inputs);
    for (size_t i = 0; i < n_inputs; i++) {
        if (offsets[i].native() != elements.size() - input.size()) {
            return GraphEvalError::InvalidInput;
        }
        BOOST_OUTCOME_TRY(auto tensor, abi_decode_tensor(input));
        inputs.emplace_back(std::move(tensor));
    }
    return inputs;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

GraphEvalContract::GraphEvalContract(State &state, CallTracerBase &tracer)
    : state_{state}
    , call_tracer_{tracer}
{
}

template <Traits traits>
std::pair<GraphEvalContract::PrecompileFunc, uint64_t>
GraphEvalContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return {&GraphEvalContract::precompile_fallback, FALLBACK_COST};
    }

    auto const signature = load_be_unsafe<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    switch (signature) {
    case PrecompileSelector::EVAL_OP:
        return {&GraphEvalContract::precompile_eval_op<traits>, EVAL_OP_COST};
    case PrecompileSelector::EVAL_GRAPH:
        return {
            &GraphEvalContract::precompile_eval_graph<traits>, EVAL_GRAPH_COST};
    default:
        return {&GraphEvalContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_MONAD_TRAITS(GraphEvalContract::precompile_dispatch);

Result<void> function_not_payable(uint256_be_t const &value)
{
    bool const all_zero = std::all_of(
        value.bytes,
        value.bytes + sizeof(uint256_be_t),
        [](uint8_t const byte) { return byte == 0; });

    if (MONAD_UNLIKELY(!all_zero)) {
        return GraphEvalError::ValueNonZero;
    }
    return outcome::success();
}

Result<Tensor> op_matmul(std::vector<Tensor> const &inputs)
{
    if (MONAD_UNLIKELY(inputs.size() != 2)) {
        return GraphEvalError::ArityError;
    }

    auto const &x = inputs[0];
    auto const &y = inputs[1];

    if (x.dtype() != Dtype::int8 || y.dtype() != Dtype::int8) {
        return GraphEvalError::TypeError;
    }

    // TODO: support batched matmul
    if (x.rank() != 2 || y.rank() != 2) {
        return GraphEvalError::RankError;
    }

    uint16_t const m = x.dimensions()[0];
    uint16_t const k = x.dimensions()[1];
    uint16_t const n = y.dimensions()[1];
    if (y.dimensions()[0] != k) {
        return GraphEvalError::ShapeError;
    }

    // TODO: charge gas for m * k * n and the output size; m and n up to 65535
    // make this a ~17GB allocation
    // Empty shapes are handled here rather than passing zero-sized buffers to
    // IREE.
    size_t const size = size_t{m} * size_t{n} * dtype_size(Dtype::int32);
    uint8_t *data =
        static_cast<uint8_t *>(std::aligned_alloc(IREE_ALIGNMENT, size));
    Tensor result{Dtype::int32, {2, {m, n}}, data};
    if (m != 0 && n != 0) {
        std::vector<Tensor> inputs{x, y};
        Kernel("module.matmul_i8")(inputs, result);
    }

    return result;
}

template <Traits traits>
Result<byte_string> GraphEvalContract::precompile_eval_op(
    byte_string_view input, Address const &, uint256_be_t const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    // Static: read uint16_t
    BOOST_OUTCOME_TRY(auto const opcode_id_be, abi_decode_fixed<u16_be>(input));
    uint16_t const opcode_id_16 = opcode_id_be.native();
    if (opcode_id_16 != static_cast<uint16_t>(Op::MatMul)) {
        return GraphEvalError::InvalidOp;
    }
    auto const opcode_id = static_cast<Op>(opcode_id_16);

    // Dynamic: read head(Tensor[]), the offset of its tail, which the
    // canonical encoding puts right after the two head words
    BOOST_OUTCOME_TRY(auto const inputs_head, abi_decode_fixed<u256_be>(input));
    if (inputs_head.native() != 2 * 32) {
        return GraphEvalError::InvalidInput;
    }

    // Dynamic: read tail(Tensor[])
    BOOST_OUTCOME_TRY(
        auto const inputs, abi_decode_dynamic_tensor_array_tail(input));
    switch (opcode_id) {
    case Op::MatMul: {
        BOOST_OUTCOME_TRY(auto const result, op_matmul(inputs));
        // abi.encode(result): Tensor is a dynamic tuple, so its offset comes
        // first, then the tuple itself
        byte_string output;
        output += abi_encode_uint(u256_be{sizeof(bytes32_t)});
        abi_append_tensor(result, output);
        return output;
    }
    default:
        return GraphEvalError::InvalidOp;
    }

    return GraphEvalError::TypeError;
}

EXPLICIT_MONAD_TRAITS_MEMBER(GraphEvalContract::precompile_eval_op);

template <Traits traits>
Result<byte_string> GraphEvalContract::precompile_eval_graph(
    byte_string_view input, Address const &, uint256_be_t const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(msg_value));

    // Static: read GraphRef
    BOOST_OUTCOME_TRY(
        auto const graph_address, abi_decode_fixed<Address>(input));

    // Dynamic: read head(Tensor[]), the offset of its tail, which the
    // canonical encoding puts right after the two head words
    BOOST_OUTCOME_TRY(auto const inputs_head, abi_decode_fixed<u256_be>(input));
    if (inputs_head.native() != 2 * 32) {
        return GraphEvalError::InvalidInput;
    }

    BOOST_OUTCOME_TRY(auto inputs, abi_decode_dynamic_tensor_array_tail(input));

    // Get a hold of the graphcode
    auto const code = state_.read_code(state_.get_code_hash(graph_address));
    // For now this reads the intercode and interprets it as raw graphcode.
    auto const *graphcode = code->intercode()->code();
    auto const graphcode_size = code->intercode()->size();

    Interpreter interpreter{state_, std::move(inputs), graphcode, graphcode_size};

    BOOST_OUTCOME_TRY(auto const outputs, interpreter.run());

    byte_string output{abi_encode_uint(u64_be{outputs.size()})};
    for (auto const &out_tensor : outputs) {
        abi_append_tensor(out_tensor, output);
    }
    return output;
}

EXPLICIT_MONAD_TRAITS_MEMBER(GraphEvalContract::precompile_eval_graph);

Result<byte_string> GraphEvalContract::precompile_fallback(
    byte_string_view const, Address const &, uint256_be_t const &)
{
    return GraphEvalError::MethodNotSupported;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
