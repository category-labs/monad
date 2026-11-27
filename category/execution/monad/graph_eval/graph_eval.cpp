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
#include <category/core/math.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/fine_interpreter.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <span>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

//
// Function Selectors
//

struct PrecompileSelector
{
    // TODO: evalOp still takes the Tensor[] evalGraph took before TensorInput.
    // It isn't implemented; update it with it, or delete it
    static constexpr uint32_t EVAL_OP =
        abi_encode_selector("evalOp(uint16,(uint8,uint16[],bytes)[])");

    static constexpr uint32_t EVAL_GRAPH = abi_encode_selector(
        "evalGraph(address,((uint8,uint16[]),uint8,bytes)[])");
};

//
// Gas costs (dummy)
//

// TODO: charge for reading tensors by reference
constexpr uint64_t EVAL_OP_COST = 100;
constexpr uint64_t EVAL_GRAPH_COST = 100;
constexpr uint64_t FALLBACK_COST = 100;

//
// Limits
//

constexpr uint64_t MAX_INPUTS = 16;

// ABI-decode tail(T[]), for a dynamic tuple type T: a 256-bit length, then
// each element's offset from the end of the length, then the elements, which
// `decode` reads. They're read in place, so only the canonical layout is
// accepted, each element right after the one before
template <typename T, size_t max_length>
Result<std::vector<T>> abi_decode_dynamic_array_tail(
    byte_string_view &input, Result<T> (*const decode)(byte_string_view &))
{
    BOOST_OUTCOME_TRY(auto const length_be, abi_decode_fixed<u256_be>(input));
    auto const length_256 = length_be.native();
    if (length_256.as_words()[1] || length_256.as_words()[2] ||
        length_256.as_words()[3]) {
        return GraphEvalError::ArityError;
    }
    auto const length = length_256.as_words()[0];
    if (length > max_length) {
        return GraphEvalError::ArityError;
    }

    byte_string_view const elements = input;
    std::array<u256_be, max_length> offsets{};
    for (size_t i = 0; i < length; i++) {
        BOOST_OUTCOME_TRY(offsets[i], abi_decode_fixed<u256_be>(input));
    }

    std::vector<T> result;
    result.reserve(length);
    for (size_t i = 0; i < length; i++) {
        if (offsets[i].native() != elements.size() - input.size()) {
            return GraphEvalError::InvalidInput;
        }
        BOOST_OUTCOME_TRY(auto const element, decode(input));
        result.push_back(element);
    }
    return result;
}

// Thread-local memory arena
struct ThreadArena
{
    uint8_t *const data;

    ThreadArena()
        : data(static_cast<uint8_t *>(
              std::aligned_alloc(TENSOR_DATA_ALIGNMENT, ARENA_SIZE)))
    {
        MONAD_ASSERT(data != nullptr);
    }

    ~ThreadArena()
    {
        std::free(data);
    }

    ThreadArena(ThreadArena const &) = delete;
    ThreadArena &operator=(ThreadArena const &) = delete;
};

uint8_t *thread_arena()
{
    thread_local ThreadArena arena;
    return arena.data;
}

// Runs the graph in `graph_address`'s code on `inputs`, in the thread's arena
Result<GraphOutputs> run_graph(
    State &state, Address const &graph_address,
    std::span<TensorInput const> const inputs)
{
    // Get a hold of the graphcode
    auto const code = state.read_code(state.get_code_hash(graph_address));
    auto const &graphcode{code->intercode()->graphcode()};
    if (!graphcode) {
        // If the graphcode isn't available, this means we're trying to
        // execute code that wasn't a graph at all.
        return GraphEvalError::GraphValidationError;
    }
    FineInterpreter interpreter{*graphcode, state, inputs, thread_arena()};
    return interpreter.run();
}

// abi.encode(tensors), as Solidity returns a Tensor[]: the offset of the
// array, its length, each tensor's offset from the end of the length, then the
// tensors, each with its elements big-endian. Each offset is filled in once its
// tensor's place is known
byte_string abi_encode_tensors(std::span<Tensor const> const tensors)
{
    byte_string output;
    output += abi_encode_uint(u64_be{32});
    output += abi_encode_uint(u64_be{tensors.size()});
    size_t const elements_start = output.size();
    output.append(32 * tensors.size(), 0);
    for (size_t i = 0; i < tensors.size(); i++) {
        bytes32_t const offset =
            abi_encode_uint(u64_be{output.size() - elements_start});
        std::memcpy(
            output.data() + elements_start + 32 * i,
            offset.bytes,
            sizeof(offset.bytes));
        abi_append_tensor(tensors[i], output);
    }
    return output;
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

// TODO: under DELEGATECALL, no value is transferred, msg.value being the
// caller's own, so the check that the precompile isn't paid is skipped. It
// used to be there for every call, and rejected payable callers that had been
// paid
Result<void> check_not_paid(CallContext const &call)
{
    if (call.delegatecall) {
        return outcome::success();
    }
    return function_not_payable(call.value);
}

template <Traits traits>
Result<byte_string> GraphEvalContract::precompile_eval_op(
    byte_string_view input, CallContext const &call)
{
    // TODO: Use the interpreter's kernels for this.
    (void)input;
    (void)call;
    return GraphEvalError::InternalError;
}

EXPLICIT_MONAD_TRAITS_MEMBER(GraphEvalContract::precompile_eval_op);

// evalGraph(address graph, TensorInput[] inputs) returns (Tensor[] outputs)
template <Traits traits>
Result<byte_string> GraphEvalContract::precompile_eval_graph(
    byte_string_view input, CallContext const &call)
{
    BOOST_OUTCOME_TRY(check_not_paid(call));

    // Static: read GraphRef
    BOOST_OUTCOME_TRY(
        auto const graph_address, abi_decode_fixed<Address>(input));

    // Dynamic: read head(TensorInput[]), the offset of its tail, which the
    // canonical encoding puts right after the two head words
    BOOST_OUTCOME_TRY(auto const inputs_head, abi_decode_fixed<u256_be>(input));
    if (inputs_head.native() != 2 * 32) {
        return GraphEvalError::InvalidInput;
    }

    BOOST_OUTCOME_TRY(
        auto inputs,
        (abi_decode_dynamic_array_tail<TensorInput, MAX_INPUTS>(
            input, abi_decode_tensor_input)));

    BOOST_OUTCOME_TRY(
        auto const outputs, run_graph(state_, graph_address, inputs));
    return abi_encode_tensors({outputs.begin(), outputs.end()});
}

EXPLICIT_MONAD_TRAITS_MEMBER(GraphEvalContract::precompile_eval_graph);

Result<byte_string> GraphEvalContract::precompile_fallback(
    byte_string_view const, CallContext const &)
{
    return GraphEvalError::MethodNotSupported;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
