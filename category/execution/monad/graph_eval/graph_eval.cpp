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
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
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
#include <optional>
#include <span>
#include <utility>
#include <variant>
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
        "evalGraph(address,(uint8,uint16[],uint8,uint8,bytes)[])");

    static constexpr uint32_t EVAL_GRAPH_INTO = abi_encode_selector(
        "evalGraphInto(address,(uint8,uint16[],uint8,uint8,bytes)[],(uint8,"
        "uint8,bytes)[])");
};

//
// Gas costs (dummy)
//

// TODO: charge for reading and writing tensors by reference, per page
constexpr uint64_t EVAL_OP_COST = 100;
constexpr uint64_t EVAL_GRAPH_COST = 100;
constexpr uint64_t EVAL_GRAPH_INTO_COST = 100;
constexpr uint64_t FALLBACK_COST = 100;

//
// Limits
//

constexpr uint64_t MAX_INPUTS = 16;
constexpr uint64_t MAX_OUTPUTS = 16;

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

// The caller's storage, for storage references, through State, so that the
// precompile's reads and writes are part of the transaction's. Each access
// warms its slot, and under MIP-8 each write is recorded for its page, as for
// SLOAD and SSTORE, for the gas of later accesses in the transaction; the
// precompile itself doesn't charge for them yet
template <Traits traits>
class StateCallerStorage final : public CallerStorage
{
    State &state_;
    Address const address_;

public:
    StateCallerStorage(State &state, Address const &address)
        : state_{state}
        , address_{address}
    {
    }

    bytes32_t load(bytes32_t const &slot) override
    {
        (void)state_.access_storage<traits>(address_, slot);
        return state_.get_storage(address_, slot);
    }

    void store(bytes32_t const &slot, bytes32_t const &value) override
    {
        (void)state_.access_storage<traits>(address_, slot);
        auto const status = state_.set_storage(address_, slot, value);
        if constexpr (traits::mip_8_active()) {
            (void)state_.update_page(address_, slot, status);
        }
    }
};

// StorageRefOutsideDelegateCall if any input is in storage, or any of
// `n_stored` outputs is to be stored, but the call isn't a DELEGATECALL, so
// there's no caller's storage for it to be in
Result<void> check_storage_refs(
    std::vector<TensorInput> const &inputs, size_t const n_stored,
    CallContext const &call)
{
    if (call.delegatecall) {
        return outcome::success();
    }
    bool const any_storage_input =
        std::any_of(inputs.begin(), inputs.end(), [](TensorInput const &in) {
            return std::holds_alternative<StorageRef>(in.source);
        });
    if (any_storage_input || n_stored > 0) {
        return GraphEvalError::StorageRefOutsideDelegateCall;
    }
    return outcome::success();
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

// Runs the graph in `graph_address`'s code on `inputs`, in the thread's arena.
// For evalGraphInto, `output_count` is its number of output references
Result<std::vector<Tensor>> run_graph(
    State &state, Address const &graph_address,
    std::vector<TensorInput> &&inputs, CallerStorage *const caller_storage,
    std::optional<size_t> const output_count)
{
    // Get a hold of the graphcode
    auto const code = state.read_code(state.get_code_hash(graph_address));
    auto const &graphcode{code->intercode()->graphcode()};
    if (!graphcode) {
        // If the graphcode isn't available, this means we're trying to
        // execute code that wasn't a graph at all.
        return GraphEvalError::GraphValidationError;
    }
    Interpreter interpreter{
        state,
        std::move(inputs),
        caller_storage,
        output_count,
        *graphcode,
        thread_arena()};
    return interpreter.run();
}

// abi.encode(tensors), as Solidity returns a Tensor[]: the offset of the
// array, its length, each tensor's offset from the end of the length, then the
// tensors, each with its elements in the byte order paired with it. Each
// offset is filled in once its tensor's place is known
byte_string
abi_encode_tensors(std::span<std::pair<Tensor, ByteOrder> const> const tensors)
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
        abi_append_tensor(tensors[i].first, tensors[i].second, output);
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
    case PrecompileSelector::EVAL_GRAPH_INTO:
        return {
            &GraphEvalContract::precompile_eval_graph_into<traits>,
            EVAL_GRAPH_INTO_COST};
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
    BOOST_OUTCOME_TRY(check_storage_refs(inputs, 0, call));

    StateCallerStorage<traits> caller_storage{state_, call.recipient};
    BOOST_OUTCOME_TRY(
        auto const outputs,
        run_graph(
            state_,
            graph_address,
            std::move(inputs),
            call.delegatecall ? &caller_storage : nullptr,
            std::nullopt));

    std::vector<std::pair<Tensor, ByteOrder>> returned;
    returned.reserve(outputs.size());
    for (Tensor const &output : outputs) {
        returned.emplace_back(output, ByteOrder::BigEndian);
    }
    return abi_encode_tensors(returned);
}

EXPLICIT_MONAD_TRAITS_MEMBER(GraphEvalContract::precompile_eval_graph);

// evalGraphInto(address graph, TensorInput[] inputs, TensorOutput[] outputs)
// returns (Tensor[] returned): each of the graph's outputs is returned or
// stored, as its TensorOutput says. Storing is to the caller's storage, so it
// only works under DELEGATECALL, outside a static context. The graph's outputs
// are stored only once it has run, so after every input has been read. The
// returned outputs come back in order, with the byte orders their
// TensorOutputs give.
//
// TODO: only the returned outputs come back, so when some are stored, a
// returned output's index isn't the graph's output's, which may be confusing
template <Traits traits>
Result<byte_string> GraphEvalContract::precompile_eval_graph_into(
    byte_string_view input, CallContext const &call)
{
    BOOST_OUTCOME_TRY(check_not_paid(call));

    // Static: read GraphRef
    BOOST_OUTCOME_TRY(
        auto const graph_address, abi_decode_fixed<Address>(input));

    // Dynamic: read head(TensorInput[]) and head(TensorOutput[]), the offsets
    // of their tails. The canonical encoding puts the inputs right after the
    // three head words, then the outputs
    BOOST_OUTCOME_TRY(auto const inputs_head, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(
        auto const outputs_head, abi_decode_fixed<u256_be>(input));
    if (inputs_head.native() != 3 * 32) {
        return GraphEvalError::InvalidInput;
    }

    byte_string_view const inputs_tail = input;
    BOOST_OUTCOME_TRY(
        auto inputs,
        (abi_decode_dynamic_array_tail<TensorInput, MAX_INPUTS>(
            input, abi_decode_tensor_input)));
    if (outputs_head.native() != 3 * 32 + (inputs_tail.size() - input.size())) {
        return GraphEvalError::InvalidInput;
    }
    BOOST_OUTCOME_TRY(
        auto const outputs,
        (abi_decode_dynamic_array_tail<TensorOutput, MAX_OUTPUTS>(
            input, abi_decode_tensor_output)));

    // Two stored outputs can't start at the same slot
    for (size_t i = 0; i < outputs.size(); i++) {
        for (size_t j = 0; j < i; j++) {
            if (outputs[i].destination && outputs[j].destination &&
                outputs[i].destination->slot == outputs[j].destination->slot) {
                return GraphEvalError::InvalidInput;
            }
        }
    }
    auto const stored = static_cast<size_t>(std::count_if(
        outputs.begin(), outputs.end(), [](TensorOutput const &output) {
            return output.destination.has_value();
        }));
    BOOST_OUTCOME_TRY(check_storage_refs(inputs, stored, call));
    if (call.is_static && stored > 0) {
        return GraphEvalError::StorageWriteInStaticCall;
    }

    StateCallerStorage<traits> caller_storage{state_, call.recipient};
    BOOST_OUTCOME_TRY(
        auto const results,
        run_graph(
            state_,
            graph_address,
            std::move(inputs),
            call.delegatecall ? &caller_storage : nullptr,
            outputs.size()));
    // Nor can their slots overlap, which takes their sizes, so it's checked
    // only now, before any is written
    for (size_t i = 0; i < outputs.size(); i++) {
        for (size_t j = 0; j < i; j++) {
            if (outputs[i].destination && outputs[j].destination &&
                storage_ranges_overlap(
                    *outputs[i].destination,
                    results[i].type().size_bytes(),
                    *outputs[j].destination,
                    results[j].type().size_bytes())) {
                return GraphEvalError::InvalidInput;
            }
        }
    }
    std::vector<std::pair<Tensor, ByteOrder>> returned;
    for (size_t i = 0; i < outputs.size(); i++) {
        if (outputs[i].destination) {
            store_storage_tensor(
                caller_storage,
                *outputs[i].destination,
                outputs[i].byte_order,
                results[i]);
        }
        else {
            returned.emplace_back(results[i], outputs[i].byte_order);
        }
    }
    return abi_encode_tensors(returned);
}

EXPLICIT_MONAD_TRAITS_MEMBER(GraphEvalContract::precompile_eval_graph_into);

Result<byte_string> GraphEvalContract::precompile_fallback(
    byte_string_view const, CallContext const &)
{
    return GraphEvalError::MethodNotSupported;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
