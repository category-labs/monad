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

// This file is compiled with -march=znver4, for the int8 contraction kernel's
// AVX-512 with VNNI; see category/execution/CMakeLists.txt

#include <category/core/assert.h>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/fixed_point.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/region_claude.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>
#include <category/vm/code.hpp>
#include <category/vm/interpreter/intercode.hpp>

#include <boost/outcome/try.hpp>

#include <immintrin.h>
#include <x86intrin.h>

#include <algorithm>
#include <bit>
#include <cstring>
#include <limits>
#include <optional>
#include <span>
#include <tuple>
#include <type_traits>
#include <utility>

static_assert(std::endian::native == std::endian::little);

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

struct TensorRecord
{
    RegionTensorKind kind;
    TensorType type;
    uint64_t location;
    uint64_t source;
};

// A field of the code, which can be at any alignment
template <typename T>
T load(uint8_t const *const p)
{
    T value;
    std::memcpy(&value, p, sizeof(T));
    return value;
}

struct Loop
{
    uint8_t dim;
    RegionLoopKind kind;
    uint16_t tile;
};

struct Operand
{
    RegionOperand kind;
    uint8_t index; // The slot, view or constant
};

struct Instruction
{
    RegionOp op;
    uint8_t destination; // The slot, or Store's view
    uint8_t parameter;
    std::array<Operand, 3> operands;
};

// A program's instructions, read in place, in order: their length in bytes
// follows from each one's opcode
struct Program
{
    uint8_t const *bytes;
    size_t size;
};

// A region's header, and its tables of views, constants and instructions,
// which are read in place. A Contraction's lhs and rhs are views 0 and 1
struct Region
{
    uint8_t rank;
    std::array<uint16_t, MAX_RANK> extents;
    uint8_t n_loops;
    std::array<Loop, 2 * MAX_RANK> loops;
    RegionCore core;
    uint8_t core_dim;
    uint8_t bits; // A Contraction's fractional bits
    Dtype out_dtype; // A Contraction's output dtype
    uint8_t n_views;
    uint8_t n_constants;
    uint8_t n_slots;
    uint8_t const *views;
    uint8_t const *constants;
    Program term;
    Program epilogue;

    uint8_t const *view(size_t const v) const
    {
        return views + v * view_bytes(rank);
    }

    static size_t view_bytes(size_t const rank)
    {
        return 14 + 4 * rank;
    }

    uint16_t view_tensor(size_t const v) const
    {
        return load<uint16_t>(view(v));
    }

    uint32_t view_offset(size_t const v) const
    {
        return load<uint32_t>(view(v) + 2);
    }

    // The tensor whose one element indexes the view at run time, or
    // REGION_NO_INDEX
    uint16_t view_index(size_t const v) const
    {
        return load<uint16_t>(view(v) + 6);
    }

    uint32_t view_index_stride(size_t const v) const
    {
        return load<uint32_t>(view(v) + 8);
    }

    uint16_t view_index_count(size_t const v) const
    {
        return load<uint16_t>(view(v) + 12);
    }

    uint32_t view_stride(size_t const v, size_t const d) const
    {
        return load<uint32_t>(view(v) + 14 + 4 * d);
    }

    Dtype constant_dtype(size_t const c) const
    {
        return static_cast<Dtype>(constants[c * REGION_CONSTANT_BYTES]);
    }

    uint64_t constant_value(size_t const c) const
    {
        return load<uint64_t>(constants + c * REGION_CONSTANT_BYTES + 1);
    }
};

// How a region's loops run its core: Map has none, Horizontal runs the core
// dimension in the chunk loop, Vertical right outside it
enum class Mode
{
    Map,
    Horizontal,
    Vertical,
};

constexpr size_t NO_DIM = MAX_RANK;

constexpr size_t arity(RegionOp const op)
{
    switch (op) {
    case RegionOp::Div:
    case RegionOp::Saturate:
    case RegionOp::QExp:
    case RegionOp::QInvSqrt:
    case RegionOp::Store:
    case RegionOp::Yield:
        return 1;
    case RegionOp::Where:
        return 3;
    default:
        return 2;
    }
}

constexpr bool has_destination(RegionOp const op)
{
    return op != RegionOp::Yield;
}

constexpr bool has_parameter(RegionOp const op)
{
    switch (op) {
    case RegionOp::Div:
    case RegionOp::Saturate:
    case RegionOp::QMul:
    case RegionOp::QDiv:
    case RegionOp::QExp:
    case RegionOp::QInvSqrt:
        return true;
    default:
        return false;
    }
}

constexpr size_t instruction_bytes(RegionOp const op)
{
    return 1 + size_t{has_destination(op)} + size_t{has_parameter(op)} +
           arity(op);
}

// The instruction at p, whose opcode is valid
Instruction decode(uint8_t const *const p)
{
    Instruction instruction{};
    instruction.op = static_cast<RegionOp>(p[0]);
    size_t i = 1;
    if (has_destination(instruction.op)) {
        instruction.destination = p[i++];
    }
    if (has_parameter(instruction.op)) {
        instruction.parameter = p[i++];
    }
    for (size_t k = 0; k < arity(instruction.op); k++, i++) {
        instruction.operands[k] = {
            static_cast<RegionOperand>(p[i] >> 6),
            static_cast<uint8_t>(p[i] & 0x3f)};
    }
    return instruction;
}

constexpr bool is_reduction(RegionCore const core)
{
    return core != RegionCore::None && core != RegionCore::PrefixSum;
}

Mode mode_of(Region const &region)
{
    if (region.core == RegionCore::None) {
        return Mode::Map;
    }
    return region.loops[region.n_loops - 1].dim == region.core_dim
               ? Mode::Horizontal
               : Mode::Vertical;
}

// The loops an odometer runs around the region's inner part
size_t outer_loops(Region const &region)
{
    size_t const n = region.n_loops;
    switch (mode_of(region)) {
    case Mode::Map:
        return n - 1;
    case Mode::Horizontal:
        return region.loops[n - 1].kind == RegionLoopKind::Intra ? n - 2
                                                                 : n - 1;
    case Mode::Vertical:
        return n - 2;
    }
    MONAD_ABORT();
}

template <typename E>
Result<E> read_enum(std::span<uint8_t const> &code)
{
    BOOST_OUTCOME_TRY(
        auto const value, read_next<std::underlying_type_t<E>>(code));
    if (value > static_cast<std::underlying_type_t<E>>(E::Last_valid)) {
        return GraphEvalError::GraphValidationError;
    }
    return static_cast<E>(value);
}

struct Header
{
    uint64_t arena_bytes;
    uint16_t n_tensors;
    std::span<uint8_t const> records;
    // The accounts' code that Code tensors are copied from, and the data that
    // Literal tensors are
    uint16_t n_references;
    std::span<uint8_t const> references;
    std::span<uint8_t const> literals;

    CodeRef reference(size_t const r) const
    {
        CodeRef ref{};
        uint8_t const *const p = references.data() + r * REGION_REFERENCE_BYTES;
        std::memcpy(ref.address.bytes, p, sizeof(ref.address.bytes));
        ref.offset = load<uint32_t>(p + sizeof(ref.address.bytes));
        return ref;
    }
};

Result<Header> read_header(std::span<uint8_t const> &code)
{
    BOOST_OUTCOME_TRY(auto const magic, read_next<uint16_t>(code));
    BOOST_OUTCOME_TRY(auto const version, read_next<uint16_t>(code));
    if (magic != REGION_MAGIC || version != REGION_VERSION) {
        return GraphEvalError::GraphValidationError;
    }
    Header header{};
    BOOST_OUTCOME_TRY(header.arena_bytes, read_next<uint64_t>(code));
    BOOST_OUTCOME_TRY(header.n_tensors, read_next<uint16_t>(code));
    size_t const bytes = size_t{header.n_tensors} * REGION_TENSOR_BYTES;
    if (code.size() < bytes) {
        return GraphEvalError::GraphValidationError;
    }
    header.records = code.first(bytes);
    code = code.subspan(bytes);
    BOOST_OUTCOME_TRY(header.n_references, read_next<uint16_t>(code));
    size_t const reference_bytes =
        size_t{header.n_references} * REGION_REFERENCE_BYTES;
    if (code.size() < reference_bytes) {
        return GraphEvalError::GraphValidationError;
    }
    header.references = code.first(reference_bytes);
    code = code.subspan(reference_bytes);
    BOOST_OUTCOME_TRY(auto const literal_bytes, read_next<uint32_t>(code));
    if (code.size() < literal_bytes) {
        return GraphEvalError::GraphValidationError;
    }
    header.literals = code.first(literal_bytes);
    code = code.subspan(literal_bytes);
    return header;
}

Result<TensorRecord> read_tensor(Header const &header, uint16_t const id)
{
    if (id >= header.n_tensors) {
        return GraphEvalError::GraphValidationError;
    }
    auto record = header.records.subspan(
        size_t{id} * REGION_TENSOR_BYTES, REGION_TENSOR_BYTES);
    BOOST_OUTCOME_TRY(auto const kind, read_enum<RegionTensorKind>(record));
    BOOST_OUTCOME_TRY(auto const dtype, read_next<Dtype>(record));
    BOOST_OUTCOME_TRY(auto const rank, read_next<uint8_t>(record));
    if (rank > MAX_RANK) {
        return GraphEvalError::RankError;
    }
    std::array<uint16_t, MAX_RANK> dimensions{};
    for (auto &dimension : dimensions) {
        BOOST_OUTCOME_TRY(dimension, read_next<uint16_t>(record));
    }
    BOOST_OUTCOME_TRY(auto const location, read_next<uint32_t>(record));
    BOOST_OUTCOME_TRY(auto const source, read_next<uint32_t>(record));
    BOOST_OUTCOME_TRY(auto const shape, Shape::checked(rank, dimensions));
    BOOST_OUTCOME_TRY(auto const type, TensorType::checked(dtype, shape));
    return TensorRecord{kind, type, location, source};
}

// The fields of a record that read_tensor has accepted, read without checks
struct TensorFields
{
    RegionTensorKind kind;
    Dtype dtype;
    uint64_t count;
    uint64_t location;
    uint64_t source;
};

TensorFields tensor_fields(Header const &header, uint16_t const id)
{
    uint8_t const *const record =
        header.records.data() + size_t{id} * REGION_TENSOR_BYTES;
    TensorFields fields{
        static_cast<RegionTensorKind>(record[0]),
        static_cast<Dtype>(record[1]),
        1,
        load<uint32_t>(record + 3 + 2 * MAX_RANK),
        load<uint32_t>(record + 7 + 2 * MAX_RANK)};
    for (size_t d = 0; d < record[2]; d++) {
        fields.count *= load<uint16_t>(record + 3 + 2 * d);
    }
    return fields;
}

// Reads a region's header and finds its tables, which stay in the code. The
// counts and the enumerations in the header are checked in both passes; the
// tables' contents only by the validator
Result<void> read_region(std::span<uint8_t const> &code, Region &region)
{
    if (code.size() < REGION_HEADER_BYTES) {
        return GraphEvalError::GraphValidationError;
    }
    uint8_t const *const header = code.data();
    region.rank = header[0];
    region.n_loops = header[1];
    region.core_dim = header[3];
    region.n_views = header[4];
    region.n_constants = header[5];
    region.n_slots = header[6];
    size_t const term_bytes = header[7];
    size_t const epilogue_bytes = header[8];
    region.bits = header[9];
    if (region.rank == 0 || region.rank > MAX_RANK) {
        return GraphEvalError::RankError;
    }
    if (header[2] > static_cast<uint8_t>(RegionCore::Last_valid) ||
        region.n_loops == 0 || region.n_loops > 2 * region.rank ||
        region.n_views > REGION_MAX_VIEWS ||
        region.n_constants > REGION_MAX_CONSTANTS ||
        region.n_slots > REGION_MAX_SLOTS ||
        header[10] > static_cast<uint8_t>(Dtype::Last_valid_dtype)) {
        return GraphEvalError::GraphValidationError;
    }
    region.core = static_cast<RegionCore>(header[2]);
    region.out_dtype = static_cast<Dtype>(header[10]);
    size_t const size = REGION_HEADER_BYTES + 2 * region.rank +
                        4 * region.n_loops +
                        region.n_views * Region::view_bytes(region.rank) +
                        region.n_constants * REGION_CONSTANT_BYTES +
                        term_bytes + epilogue_bytes;
    if (code.size() < size) {
        return GraphEvalError::GraphValidationError;
    }

    uint8_t const *p = header + REGION_HEADER_BYTES;
    for (size_t d = 0; d < region.rank; d++, p += 2) {
        region.extents[d] = load<uint16_t>(p);
    }
    for (size_t l = 0; l < region.n_loops; l++, p += 4) {
        if (p[1] > static_cast<uint8_t>(RegionLoopKind::Last_valid)) {
            return GraphEvalError::GraphValidationError;
        }
        region.loops[l] = {
            p[0], static_cast<RegionLoopKind>(p[1]), load<uint16_t>(p + 2)};
    }
    region.views = p;
    p += region.n_views * Region::view_bytes(region.rank);
    region.constants = p;
    p += region.n_constants * REGION_CONSTANT_BYTES;
    region.term = {p, term_bytes};
    region.epilogue = {p + term_bytes, epilogue_bytes};
    code = code.subspan(size);
    return outcome::success();
}

// The dtype of an instruction's result, from its operands'. Div's denominator
// is checked by the validator, which has the constants
Result<Dtype>
output_dtype(Instruction const &instruction, std::array<Dtype, 3> const &in)
{
    auto const bits_ok = [&] {
        return instruction.parameter <= MAX_FRACTIONAL_BITS;
    };
    switch (instruction.op) {
    case RegionOp::Add:
    case RegionOp::Sub:
    case RegionOp::Max:
    case RegionOp::Min:
        if (in[0] != in[1]) {
            return GraphEvalError::TypeError;
        }
        return in[0];
    case RegionOp::Mul:
        if (in[0] != in[1]) {
            return GraphEvalError::TypeError;
        }
        return widened_dtype(in[0]);
    case RegionOp::Lt:
    case RegionOp::Le:
    case RegionOp::Eq:
    case RegionOp::Ge:
    case RegionOp::Gt:
        if (in[0] != in[1]) {
            return GraphEvalError::TypeError;
        }
        return Dtype::uint8;
    case RegionOp::Div:
        return in[0];
    case RegionOp::Saturate:
        if (instruction.parameter >
            static_cast<uint8_t>(Dtype::Last_valid_dtype)) {
            return GraphEvalError::TypeError;
        }
        return static_cast<Dtype>(instruction.parameter);
    case RegionOp::Where:
        if (in[0] != Dtype::uint8 || in[1] != in[2]) {
            return GraphEvalError::TypeError;
        }
        return in[1];
    case RegionOp::QMul:
    case RegionOp::QDiv:
        if (!bits_ok()) {
            return GraphEvalError::GraphValidationError;
        }
        if (in[0] != in[1]) {
            return GraphEvalError::TypeError;
        }
        return in[0];
    case RegionOp::QExp:
    case RegionOp::QInvSqrt:
        if (!bits_ok()) {
            return GraphEvalError::GraphValidationError;
        }
        return in[0];
    case RegionOp::Store:
    case RegionOp::Yield:
        return in[0];
    }
    MONAD_ABORT();
}

// The dtype a term yields, from its views' and constants' dtypes
Result<Dtype> yield_dtype(
    Program const &program, std::array<Dtype, REGION_MAX_VIEWS> const &views,
    std::array<Dtype, REGION_MAX_CONSTANTS> const &constants)
{
    std::array<Dtype, REGION_MAX_SLOTS> slots{};
    for (size_t at = 0; at < program.size;) {
        Instruction const instruction = decode(program.bytes + at);
        at += instruction_bytes(instruction.op);
        std::array<Dtype, 3> in{};
        for (size_t k = 0; k < arity(instruction.op); k++) {
            Operand const &operand = instruction.operands[k];
            switch (operand.kind) {
            case RegionOperand::Slot:
                in[k] = slots[operand.index];
                break;
            case RegionOperand::View:
                in[k] = views[operand.index];
                break;
            case RegionOperand::Constant:
                in[k] = constants[operand.index];
                break;
            case RegionOperand::Core:
                break;
            }
        }
        BOOST_OUTCOME_TRY(auto const dtype, output_dtype(instruction, in));
        if (instruction.op == RegionOp::Yield) {
            return dtype;
        }
        slots[instruction.destination & 0x3f] = dtype;
    }
    return GraphEvalError::GraphValidationError;
}

//
// Validation
//

// Whether the code at `ref` holds a tensor of `type`, as load_code_tensor
// checks it
Result<void>
check_code_tensor(State &state, CodeRef const &ref, TensorType const &type)
{
    vm::SharedVarcode const varcode = state.get_code(ref.address);
    std::span<uint8_t const> code = varcode->intercode()->code_span();
    if (ref.offset == 0 || ref.offset >= code.size() || code[0] != 0x00) {
        return GraphEvalError::InvalidTensorRef;
    }
    code = code.subspan(ref.offset);
    auto const tensor =
        read_next<std::tuple<TensorType, std::span<uint8_t const>>>(code);
    if (tensor.has_error() || std::get<0>(tensor.value()) != type) {
        return GraphEvalError::InvalidTensorRef;
    }
    return outcome::success();
}

struct ByteRange
{
    uint64_t begin;
    uint64_t end;
};

// Validates a code, either for one call, against its inputs and the accounts'
// code in `state`, or once per code, with no state, leaving the inputs' types
// to check_inputs on each run, and the Code tensors' types to the copying of
// them, as load_code_tensor checks them
class Validator
{
    Header const &header_;
    std::span<Tensor const> inputs_;
    State *const state_;
    // A bit per tensor: whether it can be read. Only the first n_tensors bits
    // are cleared, by check_tensors
    std::array<uint64_t, (std::numeric_limits<uint16_t>::max() + 1) / 64>
        written_;

    // The region being checked
    Region const *region_ = nullptr;
    std::array<ByteRange, REGION_MAX_VIEWS> reads_;
    size_t n_reads_ = 0;
    std::array<ByteRange, REGION_MAX_VIEWS> stores_;
    size_t n_stores_ = 0;
    std::array<uint16_t, REGION_MAX_VIEWS> stored_;
    // A bit per view: whether its bytes are in reads_ or stores_ yet. Views
    // can be used many times, but are recorded once
    uint64_t read_views_ = 0;
    uint64_t stored_views_ = 0;

    bool is_written(uint16_t const id) const
    {
        return (written_[id / 64] >> (id % 64)) & 1;
    }

    void set_written(uint16_t const id)
    {
        written_[id / 64] |= uint64_t{1} << (id % 64);
    }

    Result<void> check_tensors();
    Result<void> check_loops() const;
    Result<Dtype> check_view(size_t view, size_t skip, bool store);
    Result<Dtype>
    check_program(Program const &, bool term, std::optional<Dtype> core);
    Result<void> check_region(Region const &);
    Result<void> check_compose(std::span<uint8_t const> &code);

public:
    Validator(
        Header const &header, std::span<Tensor const> const inputs,
        State *const state)
        : header_(header)
        , inputs_(inputs)
        , state_(state)
    {
    }

    Result<void> validate(std::span<uint8_t const> code);
};

// The inputs' types, against the Input tensors' records, for code validated
// once: TypeError for one that differs
Result<void>
check_inputs(Header const &header, std::span<Tensor const> const inputs)
{
    for (uint16_t id = 0; id < header.n_tensors; id++) {
        uint8_t const *const record =
            header.records.data() + size_t{id} * REGION_TENSOR_BYTES;
        if (static_cast<RegionTensorKind>(record[0]) !=
            RegionTensorKind::Input) {
            continue;
        }
        uint32_t const location = load<uint32_t>(record + 3 + 2 * MAX_RANK);
        if (location >= inputs.size()) {
            return GraphEvalError::GraphValidationError;
        }
        TensorType const &type = inputs[location].type();
        Shape const &shape = type.shape();
        if (record[1] != static_cast<uint8_t>(type.dtype()) ||
            record[2] != shape.rank()) {
            return GraphEvalError::TypeError;
        }
        for (size_t d = 0; d < shape.rank(); d++) {
            if (load<uint16_t>(record + 3 + 2 * d) != shape.dimensions()[d]) {
                return GraphEvalError::TypeError;
            }
        }
    }
    return outcome::success();
}

Result<void> Validator::check_tensors()
{
    std::fill_n(written_.begin(), (header_.n_tensors + 63) / 64, uint64_t{0});
    for (uint16_t id = 0; id < header_.n_tensors; id++) {
        BOOST_OUTCOME_TRY(auto const tensor, read_tensor(header_, id));
        if (tensor.kind == RegionTensorKind::Input) {
            if (state_ == nullptr) {
                if (tensor.location >= MAX_GRAPH_INPUTS) {
                    return GraphEvalError::GraphValidationError;
                }
            }
            else {
                if (tensor.location >= inputs_.size()) {
                    return GraphEvalError::GraphValidationError;
                }
                if (inputs_[tensor.location].type() != tensor.type) {
                    return GraphEvalError::TypeError;
                }
            }
            set_written(id);
        }
        else {
            uint64_t end;
            if (tensor.location % TENSOR_DATA_ALIGNMENT != 0 ||
                __builtin_add_overflow(
                    tensor.location, tensor.type.size_bytes(), &end) ||
                end > header_.arena_bytes) {
                return GraphEvalError::GraphValidationError;
            }
        }
        if (tensor.kind == RegionTensorKind::Code) {
            if (tensor.source >= header_.n_references) {
                return GraphEvalError::GraphValidationError;
            }
            if (state_ != nullptr) {
                BOOST_OUTCOME_TRY(check_code_tensor(
                    *state_, header_.reference(tensor.source), tensor.type));
            }
            set_written(id);
        }
        else if (tensor.kind == RegionTensorKind::Literal) {
            uint64_t end;
            if (__builtin_add_overflow(
                    tensor.source, tensor.type.size_bytes(), &end) ||
                end > header_.literals.size()) {
                return GraphEvalError::GraphValidationError;
            }
            set_written(id);
        }
    }
    return outcome::success();
}

Result<void> Validator::check_loops() const
{
    Region const &region = *region_;
    enum class Coverage : uint8_t
    {
        None,
        Tiled,
        Done,
    };
    std::array<Coverage, MAX_RANK> coverage{};
    std::array<uint16_t, MAX_RANK> tiles{};
    for (size_t l = 0; l < region.n_loops; l++) {
        Loop const &loop = region.loops[l];
        if (loop.dim >= region.rank) {
            return GraphEvalError::GraphValidationError;
        }
        Coverage &state = coverage[loop.dim];
        switch (loop.kind) {
        case RegionLoopKind::Whole:
            if (state != Coverage::None || loop.tile != 0) {
                return GraphEvalError::GraphValidationError;
            }
            state = Coverage::Done;
            break;
        case RegionLoopKind::Tile:
            if (state != Coverage::None || loop.tile == 0) {
                return GraphEvalError::GraphValidationError;
            }
            state = Coverage::Tiled;
            tiles[loop.dim] = loop.tile;
            break;
        case RegionLoopKind::Intra:
            if (state != Coverage::Tiled || loop.tile != tiles[loop.dim]) {
                return GraphEvalError::GraphValidationError;
            }
            state = Coverage::Done;
            break;
        }
    }
    for (size_t d = 0; d < region.rank; d++) {
        if (coverage[d] != Coverage::Done) {
            return GraphEvalError::GraphValidationError;
        }
    }

    Loop const &chunk = region.loops[region.n_loops - 1];
    uint64_t const chunk_length = chunk.kind == RegionLoopKind::Whole
                                      ? region.extents[chunk.dim]
                                      : chunk.tile;
    if (chunk_length > REGION_CHUNK) {
        return GraphEvalError::GraphValidationError;
    }

    if (region.core == RegionCore::None) {
        return outcome::success();
    }
    size_t const c = region.core_dim;
    if (c >= region.rank) {
        return GraphEvalError::GraphValidationError;
    }
    size_t const n = region.n_loops;
    if (chunk.dim == c) {
        if (chunk.kind == RegionLoopKind::Intra &&
            (region.loops[n - 2].dim != c ||
             region.loops[n - 2].kind != RegionLoopKind::Tile)) {
            return GraphEvalError::GraphValidationError;
        }
    }
    else if (
        n < 2 || region.loops[n - 2].dim != c ||
        region.loops[n - 2].kind != RegionLoopKind::Whole) {
        return GraphEvalError::GraphValidationError;
    }
    if (is_reduction(region.core) && region.core != RegionCore::Sum &&
        region.core != RegionCore::Contraction && region.extents[c] == 0) {
        return GraphEvalError::ShapeError;
    }
    return outcome::success();
}

// Checks a view that reads or stores at the region's points, all of them or,
// with `skip`, all of them at once along that dimension, along which its stride
// must then be 0. A stored view must reach every element of its tensor once
Result<Dtype>
Validator::check_view(size_t const v, size_t const skip, bool const store)
{
    Region const &region = *region_;
    if (v >= region.n_views) {
        return GraphEvalError::GraphValidationError;
    }
    uint16_t const id = region.view_tensor(v);
    if (id >= header_.n_tensors) {
        return GraphEvalError::GraphValidationError;
    }
    TensorFields const tensor = tensor_fields(header_, id);
    uint64_t const count = tensor.count;
    if (skip != NO_DIM && region.view_stride(v, skip) != 0) {
        return GraphEvalError::GraphValidationError;
    }
    if (store) {
        if (tensor.kind != RegionTensorKind::Arena ||
            (stored_views_ >> v & 1) != 0) {
            return GraphEvalError::GraphValidationError;
        }
    }
    else if (!is_written(id)) {
        return GraphEvalError::GraphValidationError;
    }

    // A run-time index: the one element of a readable tensor, read when the
    // region starts, before anything is stored, which may move the view by up
    // to count - 1 strides. A stored view can't have one, since which elements
    // it reaches wouldn't be known
    uint16_t const index = region.view_index(v);
    uint64_t const index_count = region.view_index_count(v);
    uint64_t index_reach = 0;
    if (index != REGION_NO_INDEX) {
        if (store || index >= header_.n_tensors || !is_written(index) ||
            index_count == 0) {
            return GraphEvalError::GraphValidationError;
        }
        if (tensor_fields(header_, index).count != 1) {
            return GraphEvalError::ShapeError;
        }
        if (__builtin_mul_overflow(
                index_count - 1, region.view_index_stride(v), &index_reach)) {
            return GraphEvalError::GraphValidationError;
        }
    }

    // The largest element reached, and how many points reach elements
    uint64_t const offset = region.view_offset(v);
    uint64_t largest;
    if (__builtin_add_overflow(offset, index_reach, &largest)) {
        return GraphEvalError::GraphValidationError;
    }
    uint64_t points = 1;
    std::array<std::pair<uint64_t, uint64_t>, MAX_RANK> moving{};
    size_t n_moving = 0;
    for (size_t d = 0; d < region.rank; d++) {
        if (d == skip) {
            continue;
        }
        uint64_t const extent = region.extents[d];
        if (extent == 0) {
            points = 0;
            continue;
        }
        uint64_t const stride = region.view_stride(v, d);
        uint64_t step;
        if (__builtin_mul_overflow(extent - 1, stride, &step) ||
            __builtin_add_overflow(largest, step, &largest) ||
            __builtin_mul_overflow(points, extent, &points)) {
            return GraphEvalError::GraphValidationError;
        }
        if (extent > 1) {
            moving[n_moving++] = {stride, extent};
        }
    }

    if (store) {
        // Reaching `count` elements, all within the tensor, each once
        if (points != count) {
            return GraphEvalError::GraphValidationError;
        }
        for (size_t i = 1; i < n_moving; i++) {
            for (size_t j = i; j > 0 && moving[j] < moving[j - 1]; j--) {
                std::swap(moving[j], moving[j - 1]);
            }
        }
        uint64_t reach = 1;
        for (size_t i = 0; i < n_moving; i++) {
            auto const [stride, extent] = moving[i];
            if (stride < reach) {
                return GraphEvalError::GraphValidationError;
            }
            reach = stride * extent;
        }
    }
    if (points != 0 && largest >= count) {
        return GraphEvalError::GraphValidationError;
    }

    // Inputs aren't in the arena, and are never stored
    ByteRange range{};
    if (points != 0 && tensor.kind != RegionTensorKind::Input) {
        uint64_t const size = dtype_size(tensor.dtype);
        range = {
            tensor.location + offset * size,
            tensor.location + (largest + 1) * size};
    }
    if (store) {
        stored_views_ |= uint64_t{1} << v;
        stored_[n_stores_] = id;
        stores_[n_stores_++] = range;
    }
    else if ((read_views_ >> v & 1) == 0) {
        read_views_ |= uint64_t{1} << v;
        reads_[n_reads_++] = range;
    }
    return tensor.dtype;
}

// The dtype the program yields, for a term
Result<Dtype> Validator::check_program(
    Program const &program, bool const term, std::optional<Dtype> const core)
{
    Region const &region = *region_;
    size_t const skip =
        !term && is_reduction(region.core) ? region.core_dim : NO_DIM;
    std::array<std::optional<Dtype>, REGION_MAX_SLOTS> slots{};
    std::optional<Dtype> yielded;
    size_t n_instructions = 0;
    for (size_t at = 0; at < program.size;) {
        if (program.bytes[at] > static_cast<uint8_t>(RegionOp::Last_valid)) {
            return GraphEvalError::InvalidOp;
        }
        RegionOp const op = static_cast<RegionOp>(program.bytes[at]);
        if (instruction_bytes(op) > program.size - at ||
            ++n_instructions > REGION_MAX_INSTRUCTIONS) {
            return GraphEvalError::GraphValidationError;
        }
        Instruction const instruction = decode(program.bytes + at);
        at += instruction_bytes(op);
        if ((term && op == RegionOp::Store) ||
            (!term && op == RegionOp::Yield) ||
            (op == RegionOp::Yield && at != program.size)) {
            return GraphEvalError::GraphValidationError;
        }
        std::array<Dtype, 3> in{};
        for (size_t k = 0; k < arity(op); k++) {
            Operand const &operand = instruction.operands[k];
            switch (operand.kind) {
            case RegionOperand::Slot:
                if (operand.index >= region.n_slots || !slots[operand.index]) {
                    return GraphEvalError::GraphValidationError;
                }
                in[k] = *slots[operand.index];
                break;
            case RegionOperand::View: {
                BOOST_OUTCOME_TRY(
                    in[k], check_view(operand.index, skip, false));
                break;
            }
            case RegionOperand::Constant:
                if (operand.index >= region.n_constants) {
                    return GraphEvalError::GraphValidationError;
                }
                in[k] = region.constant_dtype(operand.index);
                break;
            case RegionOperand::Core:
                if (term || !core) {
                    return GraphEvalError::GraphValidationError;
                }
                in[k] = *core;
                break;
            }
        }
        if (op == RegionOp::Div &&
            (instruction.parameter >= region.n_constants ||
             region.constant_dtype(instruction.parameter) != Dtype::int64 ||
             region.constant_value(instruction.parameter) == 0)) {
            return GraphEvalError::GraphValidationError;
        }
        BOOST_OUTCOME_TRY(auto const dtype, output_dtype(instruction, in));
        if (op == RegionOp::Yield) {
            yielded = dtype;
        }
        else if (op == RegionOp::Store) {
            BOOST_OUTCOME_TRY(
                auto const stored,
                check_view(instruction.destination, skip, true));
            if (stored != dtype) {
                return GraphEvalError::TypeError;
            }
        }
        else {
            // A slot, or a view the result is stored in, as Store does
            uint8_t const index = instruction.destination & 0x3f;
            switch (static_cast<RegionOperand>(instruction.destination >> 6)) {
            case RegionOperand::Slot:
                if (index >= region.n_slots) {
                    return GraphEvalError::GraphValidationError;
                }
                for (size_t k = 0; k < arity(op); k++) {
                    Operand const &operand = instruction.operands[k];
                    if (operand.kind == RegionOperand::Slot &&
                        operand.index == index) {
                        return GraphEvalError::GraphValidationError;
                    }
                }
                slots[index] = dtype;
                break;
            case RegionOperand::View: {
                if (term) {
                    return GraphEvalError::GraphValidationError;
                }
                BOOST_OUTCOME_TRY(
                    auto const stored, check_view(index, skip, true));
                if (stored != dtype) {
                    return GraphEvalError::TypeError;
                }
                break;
            }
            case RegionOperand::Constant:
            case RegionOperand::Core:
                return GraphEvalError::GraphValidationError;
            }
        }
    }
    if (term) {
        if (!yielded) {
            return GraphEvalError::GraphValidationError;
        }
        return *yielded;
    }
    return Dtype{};
}

Result<void> Validator::check_region(Region const &region)
{
    region_ = &region;
    n_reads_ = 0;
    n_stores_ = 0;
    read_views_ = 0;
    stored_views_ = 0;
    BOOST_OUTCOME_TRY(check_loops());
    for (size_t c = 0; c < region.n_constants; c++) {
        if (region.constant_dtype(c) > Dtype::Last_valid_dtype) {
            return GraphEvalError::TypeError;
        }
    }
    bool const has_term = region.core != RegionCore::None &&
                          region.core != RegionCore::Contraction;
    if (!has_term && region.term.size != 0) {
        return GraphEvalError::GraphValidationError;
    }

    std::optional<Dtype> core;
    if (region.core == RegionCore::Contraction) {
        BOOST_OUTCOME_TRY(auto const lhs, check_view(0, NO_DIM, false));
        BOOST_OUTCOME_TRY(auto const rhs, check_view(1, NO_DIM, false));
        if (lhs != rhs) {
            return GraphEvalError::TypeError;
        }
        if (region.bits > MAX_FRACTIONAL_BITS) {
            return GraphEvalError::GraphValidationError;
        }
        core = region.out_dtype;
    }
    else if (region.core != RegionCore::None) {
        BOOST_OUTCOME_TRY(core, check_program(region.term, true, std::nullopt));
    }
    BOOST_OUTCOME_TRY(check_program(region.epilogue, false, core));

    auto const overlap = [](ByteRange const &a, ByteRange const &b) {
        return a.begin < b.end && b.begin < a.end;
    };
    for (size_t i = 0; i < n_stores_; i++) {
        for (size_t j = 0; j < n_reads_; j++) {
            if (overlap(stores_[i], reads_[j])) {
                return GraphEvalError::GraphValidationError;
            }
        }
        for (size_t j = 0; j < i; j++) {
            if (overlap(stores_[i], stores_[j])) {
                return GraphEvalError::GraphValidationError;
            }
        }
    }
    for (size_t i = 0; i < n_stores_; i++) {
        set_written(stored_[i]);
    }
    return outcome::success();
}

// A Compose statement: its parts are written, in the arena, and their bytes,
// sorted, tile X's exactly. X has then been written
Result<void> Validator::check_compose(std::span<uint8_t const> &code)
{
    BOOST_OUTCOME_TRY(auto const id, read_next<uint16_t>(code));
    BOOST_OUTCOME_TRY(auto const n, read_next<uint8_t>(code));
    if (id >= header_.n_tensors) {
        return GraphEvalError::GraphValidationError;
    }
    TensorFields const whole = tensor_fields(header_, id);
    if (whole.kind != RegionTensorKind::Arena) {
        return GraphEvalError::GraphValidationError;
    }
    std::array<ByteRange, std::numeric_limits<uint8_t>::max()> parts;
    for (size_t i = 0; i < n; i++) {
        BOOST_OUTCOME_TRY(auto const part, read_next<uint16_t>(code));
        if (part >= header_.n_tensors || !is_written(part)) {
            return GraphEvalError::GraphValidationError;
        }
        TensorFields const fields = tensor_fields(header_, part);
        if (fields.kind == RegionTensorKind::Input) {
            return GraphEvalError::GraphValidationError;
        }
        parts[i] = {
            fields.location,
            fields.location + fields.count * dtype_size(fields.dtype)};
        for (size_t j = i; j > 0 && (parts[j].begin < parts[j - 1].begin ||
                                     (parts[j].begin == parts[j - 1].begin &&
                                      parts[j].end < parts[j - 1].end));
             j--) {
            std::swap(parts[j], parts[j - 1]);
        }
    }
    uint64_t end = whole.location;
    for (size_t i = 0; i < n; i++) {
        if (parts[i].begin != end) {
            return GraphEvalError::GraphValidationError;
        }
        end = parts[i].end;
    }
    if (end != whole.location + whole.count * dtype_size(whole.dtype)) {
        return GraphEvalError::GraphValidationError;
    }
    set_written(id);
    return outcome::success();
}

Result<void> Validator::validate(std::span<uint8_t const> code)
{
    BOOST_OUTCOME_TRY(check_tensors());
    BOOST_OUTCOME_TRY(auto const n_statements, read_next<uint16_t>(code));
    for (size_t s = 0; s < n_statements; s++) {
        BOOST_OUTCOME_TRY(auto const kind, read_enum<RegionStatement>(code));
        if (kind == RegionStatement::Region) {
            Region region;
            BOOST_OUTCOME_TRY(read_region(code, region));
            BOOST_OUTCOME_TRY(check_region(region));
        }
        else {
            BOOST_OUTCOME_TRY(check_compose(code));
        }
    }
    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(auto const id, read_next<uint16_t>(code));
        if (id >= header_.n_tensors || !is_written(id)) {
            return GraphEvalError::GraphValidationError;
        }
    }
    if (!code.empty()) {
        return GraphEvalError::GraphValidationError;
    }
    return outcome::success();
}

//
// The int8 contraction kernel: matmul_i8's, taking its operands through views
//

// k rounded up to whole 64-byte vectors
constexpr size_t padded_length(size_t const k)
{
    return (k + 63) / 64 * 64;
}

// 128 times the sum of a column copy: what dot_block's sums with it are off by
int32_t column_correction(int8_t const *const col, size_t const length)
{
    __m512i const flip = _mm512_set1_epi8(static_cast<char>(0x80));
    __m512i acc = _mm512_setzero_si512();
    for (size_t i = 0; i < length; i += 64) {
        acc = _mm512_dpbusd_epi32(acc, flip, _mm512_loadu_si512(col + i));
    }
    return _mm512_reduce_add_epi32(acc);
}

// The dot products over k elements of R rows, `x_stride` bytes apart, with C
// column copies, `col_stride` bytes apart, into sums[r][c], as matmul_i8's
// dot_block computes them: vpdpbusd multiplies unsigned bytes by signed ones,
// so the rows' bytes are flipped to x + 128, and the caller subtracts each
// column's correction. Even with k at its largest, 65535, these sums fit in 32
// bits. The rows' elements past k are masked off, so as not to read past them;
// they flip to 128, but the copies' padding is zero
template <size_t R, size_t C>
[[gnu::always_inline]] inline void dot_block(
    int8_t const *const x, size_t const x_stride, int8_t const *const cols,
    size_t const col_stride, size_t const k, int32_t (&sums)[R][C])
{
    __m512i const flip = _mm512_set1_epi8(static_cast<char>(0x80));
    __m512i acc[R][C];
#pragma GCC unroll 4
    for (size_t r = 0; r < R; r++) {
#pragma GCC unroll 4
        for (size_t c = 0; c < C; c++) {
            acc[r][c] = _mm512_setzero_si512();
        }
    }
    for (size_t i = 0; i < k; i += 64) {
        __mmask64 const mask =
            k - i >= 64 ? ~__mmask64{0} : (__mmask64{1} << (k - i)) - 1;
        __m512i xs[R];
#pragma GCC unroll 4
        for (size_t r = 0; r < R; r++) {
            xs[r] = _mm512_xor_si512(
                _mm512_maskz_loadu_epi8(mask, x + r * x_stride + i), flip);
        }
#pragma GCC unroll 4
        for (size_t c = 0; c < C; c++) {
            __m512i const col = _mm512_loadu_si512(cols + c * col_stride + i);
#pragma GCC unroll 4
            for (size_t r = 0; r < R; r++) {
                acc[r][c] = _mm512_dpbusd_epi32(acc[r][c], xs[r], col);
            }
        }
    }
#pragma GCC unroll 4
    for (size_t r = 0; r < R; r++) {
#pragma GCC unroll 4
        for (size_t c = 0; c < C; c++) {
            sums[r][c] = _mm512_reduce_add_epi32(acc[r][c]);
        }
    }
}

// The dot product of n elements of a and b, `a_stride` and `b_stride` apart
int32_t dot_i8(
    int8_t const *const a, uint64_t const a_stride, int8_t const *const b,
    uint64_t const b_stride, size_t const n)
{
    if (a_stride == 1 && b_stride == 1) {
        __m512i const flip = _mm512_set1_epi8(static_cast<char>(0x80));
        __m512i acc = _mm512_setzero_si512();
        __m512i correction = _mm512_setzero_si512();
        for (size_t i = 0; i < n; i += 64) {
            __mmask64 const mask =
                n - i >= 64 ? ~__mmask64{0} : (__mmask64{1} << (n - i)) - 1;
            __m512i const xs =
                _mm512_xor_si512(_mm512_maskz_loadu_epi8(mask, a + i), flip);
            __m512i const ys = _mm512_maskz_loadu_epi8(mask, b + i);
            acc = _mm512_dpbusd_epi32(acc, xs, ys);
            correction = _mm512_dpbusd_epi32(correction, flip, ys);
        }
        return _mm512_reduce_add_epi32(acc) -
               _mm512_reduce_add_epi32(correction);
    }
    int32_t sum = 0;
    for (size_t i = 0; i < n; i++) {
        sum += int32_t{a[i * a_stride]} * int32_t{b[i * b_stride]};
    }
    return sum;
}

// Copies n vectors of k elements, element q of vector p being
// v[p * x_stride + q * k_stride], to cols[p * length + q], zero-padded to
// `length`. Vectors contiguous along k are copied whole. Adjacent ones,
// x_stride 1, are copied 4 at a time, as matmul_i8's gather_columns copies
// columns: a 32-bit gather fetches element q of all 4, and each vector's byte
// is then split out of the words. Only the elements of the vectors are read
void copy_vectors(
    int8_t const *const v, uint64_t const x_stride, uint64_t const k_stride,
    size_t const n, size_t const k, int8_t *const cols, size_t const length)
{
    size_t p = 0;
    if (k_stride == 1) {
        for (; p < n; p++) {
            std::memcpy(cols + p * length, v + p * x_stride, k);
        }
    }
    else if (
        x_stride == 1 &&
        k_stride <= uint64_t{std::numeric_limits<int32_t>::max()} / 16) {
        __m512i const offsets = _mm512_mullo_epi32(
            _mm512_setr_epi32(
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
            _mm512_set1_epi32(static_cast<int>(k_stride)));
        for (; p + 4 <= n; p += 4) {
            for (size_t q = 0; q < k; q += 16) {
                __mmask16 const mask =
                    k - q >= 16 ? __mmask16{0xffff}
                                : static_cast<__mmask16>((1u << (k - q)) - 1);
                __m512i const words = _mm512_mask_i32gather_epi32(
                    _mm512_setzero_si512(),
                    mask,
                    offsets,
                    v + q * k_stride + p,
                    1);
#pragma GCC unroll 4
                for (size_t c = 0; c < 4; c++) {
                    _mm_storeu_si128(
                        reinterpret_cast<__m128i *>(
                            cols + (p + c) * length + q),
                        _mm512_cvtepi32_epi8(_mm512_srli_epi32(
                            words, static_cast<unsigned>(8 * c))));
                }
            }
        }
    }
    for (; p < n; p++) {
        int8_t *const col = cols + p * length;
        for (size_t q = 0; q < k; q++) {
            col[q] = v[p * x_stride + q * k_stride];
        }
    }
    for (size_t c = 0; c < n; c++) {
        std::fill(cols + c * length + k, cols + (c + 1) * length, int8_t{0});
    }
}

//
// Execution
//

// An operand's elements in a chunk: element i is at data + i * stride elements
// The type a contraction's sums of T's are shifted in: signed for a signed T,
// so that the shift rounds down
template <typename Sum, typename T>
using contraction_shift_t = std::conditional_t<
    std::is_signed_v<T>,
    std::conditional_t<sizeof(Sum) == 8, int64_t, __int128>, Sum>;

// out[p] for each of n points, as QMatMul computes it: the sum of the k
// products lhs[p * lx + q * lk] * rhs[p * rx + q * rk], wrapping in Sum, then
// shifted right by `bits` and wrapped to Out. A product is exact when Sum is
// at least twice as wide as T; otherwise, for 64-bit T's in 64-bit sums, it's
// its low 64 bits
// contract_points' sums, with each operand's stride along the points as a
// template argument where it's 0 or 1, so that GCC can vectorize the products
// along them; ANY stands for a stride given at run time
constexpr size_t ANY = 2;

template <size_t LX, size_t RX, typename Sum, typename Wide, typename T>
void add_products(
    T const *__restrict const lhs, uint64_t const lx, uint64_t const lk,
    T const *__restrict const rhs, uint64_t const rx, uint64_t const rk,
    size_t const n, size_t const k, Sum *__restrict const sums)
{
    for (size_t q = 0; q < k; q++) {
        T const *const l = lhs + q * lk;
        T const *const r = rhs + q * rk;
        for (size_t p = 0; p < n; p++) {
            auto const a = static_cast<Wide>(l[LX == ANY ? p * lx : LX * p]);
            auto const b = static_cast<Wide>(r[RX == ANY ? p * rx : RX * p]);
            sums[p] += static_cast<Sum>(a * b);
        }
    }
}

template <typename Sum, typename T, typename Out>
[[gnu::noinline]] void contract_points(
    T const *const lhs, uint64_t const lx, uint64_t const lk,
    T const *const rhs, uint64_t const rx, uint64_t const rk, size_t const n,
    size_t const k, unsigned const bits, Out *const out)
{
    using Shift = contraction_shift_t<Sum, T>;
    using Wide = std::conditional_t<2 * sizeof(T) <= sizeof(Sum), Shift, Sum>;
    std::array<Sum, REGION_CHUNK> sums;
    std::fill_n(sums.begin(), n, Sum{0});
    if (lx == 0 && rx == 1) {
        add_products<0, 1, Sum, Wide>(
            lhs, lx, lk, rhs, rx, rk, n, k, sums.data());
    }
    else if (lx == 1 && rx == 0) {
        add_products<1, 0, Sum, Wide>(
            lhs, lx, lk, rhs, rx, rk, n, k, sums.data());
    }
    else {
        add_products<ANY, ANY, Sum, Wide>(
            lhs, lx, lk, rhs, rx, rk, n, k, sums.data());
    }
    for (size_t p = 0; p < n; p++) {
        out[p] = static_cast<Out>(static_cast<Shift>(sums[p]) >> bits);
    }
}

// contract_points, with sums in 64 bits when that gives the same results as
// 128, as matmul.cpp chooses them: always for types up to 16 bits wide, whose
// sums of up to 65535 products are exact in 64 bits, and otherwise when the
// bits that reach out are all below bit 64
void contract_any(
    Dtype const dtype, Dtype const out_dtype, unsigned const bits,
    uint8_t const *const lhs, uint64_t const lx, uint64_t const lk,
    uint8_t const *const rhs, uint64_t const rx, uint64_t const rk,
    size_t const n, size_t const k, uint8_t *const out)
{
    visit_dtype(dtype, [&]<typename T>() {
        visit_dtype(out_dtype, [&]<typename Out>() {
            auto const *const l = reinterpret_cast<T const *>(lhs);
            auto const *const r = reinterpret_cast<T const *>(rhs);
            auto *const o = reinterpret_cast<Out *>(out);
            if (sizeof(T) <= 2 || bits + 8 * sizeof(Out) <= 64) {
                contract_points<uint64_t>(l, lx, lk, r, rx, rk, n, k, bits, o);
            }
            else {
                contract_points<unsigned __int128>(
                    l, lx, lk, r, rx, rk, n, k, bits, o);
            }
        });
    });
}

struct Source
{
    uint8_t const *data;
    uint64_t stride;
    Dtype dtype;
};

struct Sink
{
    uint8_t *data;
    uint64_t stride;
};

// The loops over operands that are contiguous, or one element repeated (A or B
// false), with their pointers as __restrict parameters: GCC at -O2 vectorizes
// only loops it knows don't overlap, and ignores __restrict on local pointers.
// Validation guarantees it: an instruction's slot is none of its operands',
// and a stored view's bytes are none that the region reads. The loops are out
// of line, so that the instruction handlers that call them stay small, and
// cheap to enter and leave
template <typename Out, typename T, typename F>
[[gnu::noinline]] void loop1(
    size_t const n, Out *__restrict const o, T const *__restrict const a,
    F const &f)
{
    for (size_t i = 0; i < n; i++) {
        o[i] = f(a[i]);
    }
}

template <bool A, bool B, typename Out, typename T, typename F>
[[gnu::noinline]] void loop2(
    size_t const n, Out *__restrict const o, T const *__restrict const a,
    T const *__restrict const b, F const &f)
{
    for (size_t i = 0; i < n; i++) {
        o[i] = f(a[A ? i : 0], b[B ? i : 0]);
    }
}

// Both values are loaded whatever the condition, so that the loop is a blend
template <bool A, bool B, typename T>
[[gnu::noinline]] void select_loop(
    size_t const n, T *__restrict const o, uint8_t const *__restrict const k,
    T const *__restrict const a, T const *__restrict const b)
{
    for (size_t i = 0; i < n; i++) {
        T const x = a[A ? i : 0];
        T const y = b[B ? i : 0];
        o[i] = k[i] ? x : y;
    }
}

// The loops for any other strides
template <typename Out, typename T, typename F>
[[gnu::noinline]] void strided1(
    size_t const n, Out *const o, uint64_t const os, T const *const a,
    uint64_t const as, F const &f)
{
    for (size_t i = 0; i < n; i++) {
        o[i * os] = f(a[i * as]);
    }
}

template <typename Out, typename T, typename F>
[[gnu::noinline]] void strided2(
    size_t const n, Out *const o, uint64_t const os, T const *const a,
    uint64_t const as, T const *const b, uint64_t const bs, F const &f)
{
    for (size_t i = 0; i < n; i++) {
        o[i * os] = f(a[i * as], b[i * bs]);
    }
}

template <typename T>
[[gnu::noinline]] void strided_select(
    size_t const n, T *const o, uint64_t const os, uint8_t const *const k,
    uint64_t const ks, T const *const a, uint64_t const as, T const *const b,
    uint64_t const bs)
{
    for (size_t i = 0; i < n; i++) {
        o[i * os] = k[i * ks] ? a[i * as] : b[i * bs];
    }
}

template <typename Out, typename T, typename F>
void map1(size_t const n, Sink const out, Source const x, F const &f)
{
    auto *const o = reinterpret_cast<Out *>(out.data);
    auto const *const a = reinterpret_cast<T const *>(x.data);
    if (out.stride == 1 && x.stride == 1) {
        loop1(n, o, a, f);
        return;
    }
    strided1(n, o, out.stride, a, x.stride, f);
}

template <typename Out, typename T, typename F>
void map2(
    size_t const n, Sink const out, Source const x, Source const y, F const &f)
{
    auto *const o = reinterpret_cast<Out *>(out.data);
    auto const *const a = reinterpret_cast<T const *>(x.data);
    auto const *const b = reinterpret_cast<T const *>(y.data);
    if (out.stride == 1 && x.stride <= 1 && y.stride <= 1) {
        if (x.stride == 1 && y.stride == 1) {
            loop2<true, true>(n, o, a, b, f);
        }
        else if (x.stride == 1) {
            loop2<true, false>(n, o, a, b, f);
        }
        else if (y.stride == 1) {
            loop2<false, true>(n, o, a, b, f);
        }
        else {
            loop2<false, false>(n, o, a, b, f);
        }
        return;
    }
    strided2(n, o, out.stride, a, x.stride, b, y.stride, f);
}

// Where: c ? x : y, with a uint8 condition
template <typename T>
void select(
    size_t const n, Sink const out, Source const c, Source const x,
    Source const y)
{
    auto *const o = reinterpret_cast<T *>(out.data);
    auto const *const k = c.data;
    auto const *const a = reinterpret_cast<T const *>(x.data);
    auto const *const b = reinterpret_cast<T const *>(y.data);
    if (out.stride == 1 && c.stride == 1 && x.stride <= 1 && y.stride <= 1) {
        if (x.stride == 1 && y.stride == 1) {
            select_loop<true, true>(n, o, k, a, b);
        }
        else if (x.stride == 1) {
            select_loop<true, false>(n, o, k, a, b);
        }
        else if (y.stride == 1) {
            select_loop<false, true>(n, o, k, a, b);
        }
        else {
            select_loop<false, false>(n, o, k, a, b);
        }
        return;
    }
    strided_select(n, o, out.stride, k, c.stride, a, x.stride, b, y.stride);
}

template <typename F>
void unary(size_t const n, Sink const out, Source const x, F const &f)
{
    visit_dtype(x.dtype, [&]<typename T>() {
        map1<std::invoke_result_t<F const &, T>, T>(n, out, x, f);
    });
}

template <typename F>
void binary(
    size_t const n, Sink const out, Source const x, Source const y, F const &f)
{
    visit_dtype(x.dtype, [&]<typename T>() {
        map2<std::invoke_result_t<F const &, T, T>, T>(n, out, x, y, f);
    });
}

// As the Div op divides
template <typename T>
T divide(T const x, int64_t const denominator)
{
    if constexpr (std::same_as<T, uint64_t>) {
        // x / |denominator| always fits, and negating it wraps
        uint64_t const magnitude =
            denominator < 0 ? uint64_t{0} - static_cast<uint64_t>(denominator)
                            : static_cast<uint64_t>(denominator);
        uint64_t const quotient = x / magnitude;
        return denominator < 0 ? uint64_t{0} - quotient : quotient;
    }
    else {
        // Every other T fits in int64, and INT64_MIN / -1 overflows
        if (denominator == -1) {
            return static_cast<T>(
                uint64_t{0} - static_cast<uint64_t>(static_cast<int64_t>(x)));
        }
        return static_cast<T>(static_cast<int64_t>(x) / denominator);
    }
}

// The dtype of Op's result, as output_dtype works it out for valid code
template <RegionOp Op>
Dtype result_dtype(std::array<Source, 3> const &in, uint8_t const parameter)
{
    if constexpr (Op == RegionOp::Mul) {
        return widened_dtype(in[0].dtype);
    }
    else if constexpr (
        Op == RegionOp::Lt || Op == RegionOp::Le || Op == RegionOp::Eq ||
        Op == RegionOp::Ge || Op == RegionOp::Gt) {
        return Dtype::uint8;
    }
    else if constexpr (Op == RegionOp::Saturate) {
        return static_cast<Dtype>(parameter);
    }
    else if constexpr (Op == RegionOp::Where) {
        return in[1].dtype;
    }
    else {
        return in[0].dtype;
    }
}

// Op on n elements. `parameter` is the instruction's, and `denominator`
// Div's, from the region's constants
template <RegionOp Op>
GraphEvalError apply(
    size_t const n, Sink const out, std::array<Source, 3> const &in,
    [[maybe_unused]] uint8_t const parameter,
    [[maybe_unused]] int64_t const denominator)
{
    if constexpr (Op == RegionOp::Add) {
        binary(n, out, in[0], in[1], WrappingAdd{});
    }
    else if constexpr (Op == RegionOp::Sub) {
        binary(n, out, in[0], in[1], WrappingSub{});
    }
    else if constexpr (Op == RegionOp::Mul) {
        binary(n, out, in[0], in[1], WideningMul{});
    }
    else if constexpr (Op == RegionOp::Lt) {
        binary(n, out, in[0], in[1], []<typename T>(T const a, T const b) {
            return uint8_t{a < b};
        });
    }
    else if constexpr (Op == RegionOp::Le) {
        binary(n, out, in[0], in[1], []<typename T>(T const a, T const b) {
            return uint8_t{a <= b};
        });
    }
    else if constexpr (Op == RegionOp::Eq) {
        binary(n, out, in[0], in[1], []<typename T>(T const a, T const b) {
            return uint8_t{a == b};
        });
    }
    else if constexpr (Op == RegionOp::Ge) {
        binary(n, out, in[0], in[1], []<typename T>(T const a, T const b) {
            return uint8_t{a >= b};
        });
    }
    else if constexpr (Op == RegionOp::Gt) {
        binary(n, out, in[0], in[1], []<typename T>(T const a, T const b) {
            return uint8_t{a > b};
        });
    }
    else if constexpr (Op == RegionOp::Max) {
        binary(n, out, in[0], in[1], Maximum{});
    }
    else if constexpr (Op == RegionOp::Min) {
        binary(n, out, in[0], in[1], Minimum{});
    }
    else if constexpr (Op == RegionOp::Div) {
        unary(n, out, in[0], [denominator]<typename T>(T const x) {
            return divide(x, denominator);
        });
    }
    else if constexpr (Op == RegionOp::Saturate) {
        visit_dtype(in[0].dtype, [&]<typename From>() {
            visit_dtype(static_cast<Dtype>(parameter), [&]<typename To>() {
                map1<To, From>(n, out, in[0], SaturateOp::Impl<To>{});
            });
        });
    }
    else if constexpr (Op == RegionOp::Where) {
        visit_dtype(in[1].dtype, [&]<typename T>() {
            select<T>(n, out, in[0], in[1], in[2]);
        });
    }
    else if constexpr (Op == RegionOp::QMul) {
        binary(
            n,
            out,
            in[0],
            in[1],
            [bits = unsigned{parameter}]<typename T>(T const a, T const b) {
                return q_mul(a, b, bits);
            });
    }
    else if constexpr (Op == RegionOp::QDiv) {
        return visit_dtype(in[1].dtype, [&]<typename T>() -> GraphEvalError {
            auto const *const b = reinterpret_cast<T const *>(in[1].data);
            for (size_t i = 0; i < n; i++) {
                if (b[i * in[1].stride] == 0) {
                    return GraphEvalError::DivisionByZero;
                }
            }
            map2<T, T>(
                n,
                out,
                in[0],
                in[1],
                [bits = unsigned{parameter}](T const x, T const y) {
                    return q_div(x, y, bits);
                });
            return GraphEvalError::Success;
        });
    }
    else if constexpr (Op == RegionOp::QExp) {
        unary(
            n, out, in[0], [bits = unsigned{parameter}]<typename T>(T const x) {
                return q_exp(x, bits);
            });
    }
    else if constexpr (Op == RegionOp::QInvSqrt) {
        return visit_dtype(in[0].dtype, [&]<typename T>() -> GraphEvalError {
            auto const *const a = reinterpret_cast<T const *>(in[0].data);
            for (size_t i = 0; i < n; i++) {
                T const x = a[i * in[0].stride];
                if (x == 0) {
                    return GraphEvalError::DivisionByZero;
                }
                if (std::cmp_less(x, 0)) {
                    return GraphEvalError::DomainError;
                }
            }
            map1<T, T>(n, out, in[0], [bits = unsigned{parameter}](T const x) {
                return q_inv_sqrt(x, bits);
            });
            return GraphEvalError::Success;
        });
    }
    else if constexpr (Op == RegionOp::Store) {
        unary(n, out, in[0], []<typename T>(T const x) { return x; });
    }
    return GraphEvalError::Success;
}

// One run of a program on the n elements of a chunk along dimension x: the
// core's value there, the slots' dtypes, and what the program yields
struct Frame
{
    size_t n;
    size_t x;
    Source core;
    std::array<Dtype, REGION_MAX_SLOTS> slot_dtypes;
    Source yielded;
};

// The vectors along k that contract_i8 copied to the pack buffer last, which
// later chunks reuse when they read the same ones, if `valid`
struct Packed
{
    int8_t const *data;
    uint64_t x_stride;
    uint64_t k_stride;
    size_t n;
    size_t k;
    bool valid;
};

class Executor
{
    std::span<Tensor const> inputs_;
    uint8_t *arena_;
    uint8_t *scratch_;
    Header const &header_;
    State &state_;
    RegionTimes *const times_;

    // The region being run; the point at the start of the current chunk, and
    // each view's element there, which move together; each view's strides, in
    // elements and in bytes, and its dtype; its constants, aligned for the
    // kernels to read; and the core's dtype
    Region const *region_ = nullptr;
    std::array<uint64_t, MAX_RANK> index_;
    std::array<uint8_t *, REGION_MAX_VIEWS> pointers_;
    std::array<std::array<uint64_t, MAX_RANK>, REGION_MAX_VIEWS> strides_;
    std::array<std::array<int64_t, MAX_RANK>, REGION_MAX_VIEWS> byte_strides_;
    std::array<Dtype, REGION_MAX_VIEWS> dtypes_{};
    std::array<uint64_t, REGION_MAX_CONSTANTS> constants_{};
    std::array<Dtype, REGION_MAX_CONSTANTS> constant_dtypes_{};
    Dtype core_dtype_{};
    Packed packed_{};

    uint8_t *slot(size_t const s) const
    {
        return scratch_ + s * REGION_SLOT_BYTES;
    }

    uint8_t *data(TensorFields const &tensor) const
    {
        return tensor.kind == RegionTensorKind::Input
                   ? inputs_[tensor.location].data()
                   : arena_ + tensor.location;
    }

    uint8_t *accumulator() const
    {
        return slot(REGION_MAX_SLOTS);
    }

    uint64_t *indices() const
    {
        return reinterpret_cast<uint64_t *>(slot(REGION_MAX_SLOTS + 1));
    }

    uint8_t *prefixes() const
    {
        return slot(REGION_MAX_SLOTS + 2);
    }

    int32_t *corrections() const
    {
        return reinterpret_cast<int32_t *>(slot(REGION_MAX_SLOTS + 3));
    }

    int8_t *pack() const
    {
        return reinterpret_cast<int8_t *>(
            slot(REGION_MAX_SLOTS + 3) + REGION_CHUNK * sizeof(int32_t));
    }

    // A view's elements in the chunk along x that starts at index_
    std::pair<uint8_t *, uint64_t> view_at(size_t const v, size_t const x) const
    {
        return {pointers_[v], strides_[v][x]};
    }

    // Moves the point along dimension d to `to`, and every view's element
    void move_to(size_t const d, uint64_t const to)
    {
        int64_t const delta =
            static_cast<int64_t>(to) - static_cast<int64_t>(index_[d]);
        for (size_t v = 0; v < region_->n_views; v++) {
            pointers_[v] += delta * byte_strides_[v][d];
        }
        index_[d] = to;
    }

    // An operand byte's elements in the frame's chunk
    Source operand(uint8_t const byte, Frame const &frame) const
    {
        uint8_t const index = byte & 0x3f;
        switch (static_cast<RegionOperand>(byte >> 6)) {
        case RegionOperand::Slot:
            return {slot(index), 1, frame.slot_dtypes[index]};
        case RegionOperand::View: {
            auto const [data, stride] = view_at(index, frame.x);
            return {data, stride, dtypes_[index]};
        }
        case RegionOperand::Constant:
            return {
                reinterpret_cast<uint8_t const *>(&constants_[index]),
                0,
                constant_dtypes_[index]};
        case RegionOperand::Core:
            return frame.core;
        }
        MONAD_ABORT();
    }

    template <RegionOp Op>
    static GraphEvalError
    run_instruction(Executor &, uint8_t const *instruction, Frame &);

    Result<void> bind(Region const &);
    Result<Source>
    run_program(Program const &, size_t n, size_t x, Source const &core);

    // The term's elements in the chunk along x. A term that only yields a view
    // or a constant is read without running it
    Result<Source> run_term(size_t const n, size_t const x)
    {
        Program const &term = region_->term;
        if (term.size == 2 &&
            term.bytes[0] == static_cast<uint8_t>(RegionOp::Yield)) {
            return operand(term.bytes[1], Frame{n, x, Source{}, {}, {}});
        }
        return run_program(term, n, x, Source{});
    }

    bool contract_i8(
        int8_t const *fixed, uint64_t fixed_k, int8_t const *varying,
        uint64_t varying_x, uint64_t varying_k, size_t n, size_t k,
        int32_t *sums);
    void contract(size_t n, size_t x);
    Result<void> run_vertical(size_t n, size_t x);
    Result<void> run_horizontal();
    Result<void> run_region(Region const &);

    Result<void> load_tensors();

public:
    Executor(
        std::span<uint8_t> const arena, size_t const scratch_offset,
        std::span<Tensor const> const inputs, Header const &header,
        State &state, RegionTimes *const times)
        : inputs_(inputs)
        , arena_(arena.data())
        , scratch_(arena.data() + scratch_offset)
        , header_(header)
        , state_(state)
        , times_(times)
    {
    }

    Result<RegionOutputs> run(std::span<uint8_t const> code);
};

Result<void> Executor::bind(Region const &region)
{
    region_ = &region;
    packed_.valid = false;
    for (size_t v = 0; v < region.n_views; v++) {
        TensorFields const tensor =
            tensor_fields(header_, region.view_tensor(v));
        dtypes_[v] = tensor.dtype;
        uint64_t const size = dtype_size(tensor.dtype);
        uint64_t offset = region.view_offset(v);
        if (region.view_index(v) != REGION_NO_INDEX) {
            TensorFields const index =
                tensor_fields(header_, region.view_index(v));
            uint64_t const count = region.view_index_count(v);
            std::optional<uint64_t> k;
            visit_dtype(index.dtype, [&]<typename T>() {
                T const value = load<T>(data(index));
                if (std::cmp_greater_equal(value, 0) &&
                    std::cmp_less(value, count)) {
                    k = static_cast<uint64_t>(value);
                }
            });
            if (!k) {
                return GraphEvalError::IndexError;
            }
            offset += *k * region.view_index_stride(v);
        }
        pointers_[v] = data(tensor) + offset * size;
        for (size_t d = 0; d < region.rank; d++) {
            strides_[v][d] = region.view_stride(v, d);
            byte_strides_[v][d] = static_cast<int64_t>(strides_[v][d] * size);
        }
    }
    index_.fill(0);
    for (size_t c = 0; c < region.n_constants; c++) {
        constants_[c] = region.constant_value(c);
        constant_dtypes_[c] = region.constant_dtype(c);
    }
    if (region.core == RegionCore::Contraction) {
        core_dtype_ = region.out_dtype;
    }
    else if (region.core != RegionCore::None) {
        BOOST_OUTCOME_TRY(
            core_dtype_, yield_dtype(region.term, dtypes_, constant_dtypes_));
    }
    return outcome::success();
}

// The instruction at `instruction`, whose opcode is Op: its fields are at
// offsets known from Op, and so are its result's dtype and its kernel
template <RegionOp Op>
GraphEvalError Executor::run_instruction(
    Executor &executor, uint8_t const *const instruction, Frame &frame)
{
    constexpr size_t first_operand =
        1 + size_t{has_destination(Op)} + size_t{has_parameter(Op)};
    std::array<Source, 3> in{};
    for (size_t k = 0; k < arity(Op); k++) {
        in[k] = executor.operand(instruction[first_operand + k], frame);
    }
    if constexpr (Op == RegionOp::Yield) {
        frame.yielded = in[0];
        return GraphEvalError::Success;
    }
    else {
        uint8_t const destination = instruction[1];
        uint8_t const parameter = has_parameter(Op) ? instruction[2] : 0;
        Sink out;
        uint8_t const index = destination & 0x3f;
        if (Op == RegionOp::Store ||
            destination >> 6 == static_cast<uint8_t>(RegionOperand::View)) {
            auto const [data, stride] = executor.view_at(index, frame.x);
            out = {data, stride};
        }
        else {
            frame.slot_dtypes[index] = result_dtype<Op>(in, parameter);
            out = {executor.slot(index), 1};
        }
        int64_t const denominator =
            Op == RegionOp::Div
                ? static_cast<int64_t>(executor.constants_[parameter])
                : 0;
        return apply<Op>(frame.n, out, in, parameter, denominator);
    }
}

// Runs a program on the n elements of the chunk along x that starts at
// index_, and returns what it yields. Each instruction is one jump through a
// table indexed by its opcode, which also gives its length
Result<Source> Executor::run_program(
    Program const &program, size_t const n, size_t const x, Source const &core)
{
    struct Entry
    {
        GraphEvalError (*run)(Executor &, uint8_t const *, Frame &);
        size_t length;
    };

    static constexpr auto table =
        []<size_t... I>(std::index_sequence<I...>) {
            return std::array<Entry, sizeof...(I)>{Entry{
                &run_instruction<static_cast<RegionOp>(I)>,
                instruction_bytes(static_cast<RegionOp>(I))}...};
        }(std::make_index_sequence<
            static_cast<size_t>(RegionOp::Last_valid) + 1>{});

    Frame frame{n, x, core, {}, {}};
    uint8_t const *p = program.bytes;
    uint8_t const *const end = p + program.size;
    while (p < end) {
        Entry const &entry = table[*p];
        GraphEvalError const status = entry.run(*this, p, frame);
        if (status != GraphEvalError::Success) {
            return GraphEvalError{status};
        }
        p += entry.length;
    }
    return frame.yielded;
}

// sums[p] for the n points of a vertical chunk, when one operand is the same
// at all of them and the other varies: the varying one's vectors along k are
// copied, zero-padded, into the pack, as matmul_i8 copies y's columns. False if
// they don't fit
// The n sums of a chunk of an int8 contraction, from the vector along k of the
// operand that's the same at every point, `fixed`, and those of the one that
// varies, as matmul_i8 computes its products: of each pair, the vector that's
// contiguous along k is read in place, as matmul_i8 reads the rows of x, and
// the other is copied, zero-padded to whole 64-byte vectors, as it copies the
// columns of y. With the varying vectors contiguous, the fixed one is copied,
// once for every chunk that reads it, and 4 points are computed at a time.
// Otherwise the varying ones are copied, as many at a time as the pack buffer
// holds, and kept for later chunks if they all fit. False if not even one
// fits: when k is above 32,704 and the fixed vector isn't contiguous either
bool Executor::contract_i8(
    int8_t const *const fixed, uint64_t const fixed_k,
    int8_t const *const varying, uint64_t const varying_x,
    uint64_t const varying_k, size_t const n, size_t const k,
    int32_t *const sums)
{
    if (k == 0) {
        std::fill_n(sums, n, int32_t{0});
        return true;
    }
    size_t const length = padded_length(k);
    int8_t *const cols = pack();
    int32_t *const correction = corrections();
    // Copies `count` vectors to the start of the pack buffer, and their
    // corrections, unless they're there already
    auto const copy = [&](int8_t const *const v,
                          uint64_t const x_stride,
                          uint64_t const k_stride,
                          size_t const count,
                          bool const keep) {
        if (packed_.valid && packed_.data == v &&
            packed_.x_stride == x_stride && packed_.k_stride == k_stride &&
            packed_.n == count && packed_.k == k) {
            return;
        }
        copy_vectors(v, x_stride, k_stride, count, k, cols, length);
        for (size_t p = 0; p < count; p++) {
            correction[p] = column_correction(cols + p * length, length);
        }
        packed_ = {v, x_stride, k_stride, count, k, keep};
    };

    if (varying_k == 1) {
        copy(fixed, 0, fixed_k, 1, true);
        size_t p = 0;
        for (; p + 4 <= n; p += 4) {
            int32_t block[4][1];
            dot_block<4, 1>(
                varying + p * varying_x, varying_x, cols, length, k, block);
            for (size_t r = 0; r < 4; r++) {
                sums[p + r] = block[r][0] - correction[0];
            }
        }
        for (; p < n; p++) {
            int32_t block[1][1];
            dot_block<1, 1>(varying + p * varying_x, 0, cols, length, k, block);
            sums[p] = block[0][0] - correction[0];
        }
        return true;
    }

    // The fixed vector, in place, or copied to the end of the pack buffer
    int8_t const *row = fixed;
    size_t space = REGION_PACK_BYTES;
    if (fixed_k != 1) {
        space -= length;
        int8_t *const fixed_copy = cols + space;
        for (size_t q = 0; q < k; q++) {
            fixed_copy[q] = fixed[q * fixed_k];
        }
        row = fixed_copy;
    }
    size_t const group = space / length;
    if (group == 0) {
        return false;
    }
    for (size_t p0 = 0; p0 < n; p0 += group) {
        size_t const count = std::min(group, n - p0);
        copy(varying + p0 * varying_x, varying_x, varying_k, count, count == n);
        size_t p = 0;
        for (; p + 4 <= count; p += 4) {
            int32_t block[1][4];
            dot_block<1, 4>(row, 0, cols + p * length, length, k, block);
            for (size_t c = 0; c < 4; c++) {
                sums[p0 + p + c] = block[0][c] - correction[p + c];
            }
        }
        for (; p < count; p++) {
            int32_t block[1][1];
            dot_block<1, 1>(row, 0, cols + p * length, length, k, block);
            sums[p0 + p] = block[0][0] - correction[p];
        }
    }
    return true;
}

// The accumulator's values for the n points of a vertical chunk along x
void Executor::contract(size_t const n, size_t const x)
{
    size_t const c = region_->core_dim;
    size_t const k = region_->extents[c];
    auto const [l, lx] = view_at(0, x);
    auto const [r, rx] = view_at(1, x);
    uint64_t const lk = region_->view_stride(0, c);
    uint64_t const rk = region_->view_stride(1, c);
    if (dtypes_[0] != Dtype::int8 || region_->bits != 0 ||
        core_dtype_ != Dtype::int32) {
        contract_any(
            dtypes_[0],
            core_dtype_,
            region_->bits,
            l,
            lx,
            lk,
            r,
            rx,
            rk,
            n,
            k,
            accumulator());
        return;
    }
    auto *const sums = reinterpret_cast<int32_t *>(accumulator());
    auto const *const lhs = reinterpret_cast<int8_t const *>(l);
    auto const *const rhs = reinterpret_cast<int8_t const *>(r);
    if (lx == 0 && rx != 0 && contract_i8(lhs, lk, rhs, rx, rk, n, k, sums)) {
        return;
    }
    if (rx == 0 && lx != 0 && contract_i8(rhs, rk, lhs, lx, lk, n, k, sums)) {
        return;
    }
    for (size_t p = 0; p < n; p++) {
        int32_t sum = 0;
        for (size_t q = 0; q < k; q++) {
            sum +=
                int32_t{lhs[p * lx + q * lk]} * int32_t{rhs[p * rx + q * rk]};
        }
        sums[p] = sum;
    }
}

// The term's elements are contiguous, all the same, or strided: each case gets
// its own loops, so that the first two vectorize
template <typename F>
void with_elements(Source const &term, F const &f)
{
    visit_dtype(term.dtype, [&]<typename T>() {
        auto const *const t = reinterpret_cast<T const *>(term.data);
        if (term.stride == 1) {
            f([t](size_t const i) { return t[i]; });
        }
        else if (term.stride == 0) {
            f([v = t[0]](size_t) { return v; });
        }
        else {
            f([t, s = term.stride](size_t const i) { return t[i * s]; });
        }
    });
}

// Element p of a vertical chunk's term, at(p), into its accumulator, at step k
// along the core dimension
template <typename T, typename At>
void combine_vertical(
    RegionCore const core, uint64_t const k, size_t const n,
    T *__restrict const acc, uint64_t *__restrict const index, At const &at)
{
    switch (core) {
    case RegionCore::Sum:
    case RegionCore::PrefixSum:
        for (size_t p = 0; p < n; p++) {
            acc[p] = WrappingAdd{}(acc[p], at(p));
        }
        break;
    case RegionCore::Max:
    case RegionCore::Min:
        if (k == 0) {
            for (size_t p = 0; p < n; p++) {
                acc[p] = at(p);
            }
        }
        else if (core == RegionCore::Max) {
            for (size_t p = 0; p < n; p++) {
                acc[p] = Maximum{}(acc[p], at(p));
            }
        }
        else {
            for (size_t p = 0; p < n; p++) {
                acc[p] = Minimum{}(acc[p], at(p));
            }
        }
        break;
    case RegionCore::ArgMax:
        for (size_t p = 0; p < n; p++) {
            T const v = at(p);
            if (k == 0 || acc[p] < v) {
                acc[p] = v;
                index[p] = k;
            }
        }
        break;
    case RegionCore::ArgMin:
        for (size_t p = 0; p < n; p++) {
            T const v = at(p);
            if (k == 0 || v < acc[p]) {
                acc[p] = v;
                index[p] = k;
            }
        }
        break;
    case RegionCore::None:
    case RegionCore::Contraction:
        MONAD_ABORT();
    }
}

// Elements start to start + n - 1 along the core dimension, at(i) for each i,
// into the one accumulator, or for PrefixSum, into prefixes
template <typename T, typename At>
void combine_horizontal(
    RegionCore const core, uint64_t const start, size_t const n,
    T *__restrict const acc, uint64_t *__restrict const index,
    T *__restrict const prefix, At const &at)
{
    T value = *acc;
    uint64_t position = *index;
    size_t i = 0;
    if (start == 0 && n != 0 && core != RegionCore::Sum &&
        core != RegionCore::PrefixSum) {
        value = at(0);
        position = 0;
        i = 1;
    }
    switch (core) {
    case RegionCore::Sum:
        for (; i < n; i++) {
            value = WrappingAdd{}(value, at(i));
        }
        break;
    case RegionCore::PrefixSum:
        for (; i < n; i++) {
            value = WrappingAdd{}(value, at(i));
            prefix[i] = value;
        }
        break;
    case RegionCore::Max:
        for (; i < n; i++) {
            value = Maximum{}(value, at(i));
        }
        break;
    case RegionCore::Min:
        for (; i < n; i++) {
            value = Minimum{}(value, at(i));
        }
        break;
    case RegionCore::ArgMax:
        for (; i < n; i++) {
            T const v = at(i);
            if (value < v) {
                value = v;
                position = start + i;
            }
        }
        break;
    case RegionCore::ArgMin:
        for (; i < n; i++) {
            T const v = at(i);
            if (v < value) {
                value = v;
                position = start + i;
            }
        }
        break;
    case RegionCore::None:
    case RegionCore::Contraction:
        MONAD_ABORT();
    }
    *acc = value;
    *index = position;
}

// The core along a Whole loop right outside the chunk along x, of n points
Result<void> Executor::run_vertical(size_t const n, size_t const x)
{
    Region const &region = *region_;
    size_t const c = region.core_dim;
    Source const core{accumulator(), 1, core_dtype_};
    if (region.core == RegionCore::Contraction) {
        move_to(c, 0);
        contract(n, x);
        BOOST_OUTCOME_TRY(run_program(region.epilogue, n, x, core));
        return outcome::success();
    }
    std::fill_n(accumulator(), REGION_SLOT_BYTES, uint8_t{0});
    for (uint64_t k = 0; k < region.extents[c]; k++) {
        move_to(c, k);
        BOOST_OUTCOME_TRY(auto const term, run_term(n, x));
        with_elements(term, [&](auto const &at) {
            using T = std::remove_cvref_t<decltype(at(0))>;
            combine_vertical(
                region.core,
                k,
                n,
                reinterpret_cast<T *>(accumulator()),
                indices(),
                at);
        });
        if (region.core == RegionCore::PrefixSum) {
            BOOST_OUTCOME_TRY(run_program(region.epilogue, n, x, core));
        }
    }
    if (region.core == RegionCore::PrefixSum) {
        return outcome::success();
    }
    if (region.core == RegionCore::ArgMax ||
        region.core == RegionCore::ArgMin) {
        visit_dtype(core_dtype_, [&]<typename T>() {
            auto *const acc = reinterpret_cast<T *>(accumulator());
            for (size_t p = 0; p < n; p++) {
                acc[p] = static_cast<T>(indices()[p]);
            }
        });
    }
    move_to(c, 0);
    BOOST_OUTCOME_TRY(run_program(region.epilogue, n, x, core));
    return outcome::success();
}

// The core along the innermost loops, chunk by chunk
Result<void> Executor::run_horizontal()
{
    Region const &region = *region_;
    size_t const c = region.core_dim;
    Loop const &chunk = region.loops[region.n_loops - 1];
    uint64_t const extent = region.extents[c];
    uint64_t const step =
        chunk.kind == RegionLoopKind::Intra ? chunk.tile : extent;
    Source const core{accumulator(), 0, core_dtype_};
    std::fill_n(accumulator(), sizeof(uint64_t), uint8_t{0});

    if (region.core == RegionCore::Contraction &&
        (dtypes_[0] != Dtype::int8 || region.bits != 0 ||
         core_dtype_ != Dtype::int32)) {
        move_to(c, 0);
        auto const [l, lk] = view_at(0, c);
        auto const [r, rk] = view_at(1, c);
        contract_any(
            dtypes_[0],
            core_dtype_,
            region.bits,
            l,
            0,
            lk,
            r,
            0,
            rk,
            1,
            extent,
            accumulator());
        BOOST_OUTCOME_TRY(run_program(region.epilogue, 1, c, core));
        return outcome::success();
    }
    if (region.core == RegionCore::Contraction) {
        int32_t sum = 0;
        for (uint64_t start = 0; start < extent; start += step) {
            size_t const n = std::min(step, extent - start);
            move_to(c, start);
            auto const [l, ls] = view_at(0, c);
            auto const [r, rs] = view_at(1, c);
            sum += dot_i8(
                reinterpret_cast<int8_t const *>(l),
                ls,
                reinterpret_cast<int8_t const *>(r),
                rs,
                n);
        }
        std::memcpy(accumulator(), &sum, sizeof(sum));
        move_to(c, 0);
        BOOST_OUTCOME_TRY(run_program(region.epilogue, 1, c, core));
        return outcome::success();
    }

    for (uint64_t start = 0; start < extent; start += step) {
        size_t const n = std::min(step, extent - start);
        move_to(c, start);
        BOOST_OUTCOME_TRY(auto const term, run_term(n, c));
        with_elements(term, [&](auto const &at) {
            using T = std::remove_cvref_t<decltype(at(0))>;
            combine_horizontal(
                region.core,
                start,
                n,
                reinterpret_cast<T *>(accumulator()),
                indices(),
                reinterpret_cast<T *>(prefixes()),
                at);
        });
        if (region.core == RegionCore::PrefixSum) {
            BOOST_OUTCOME_TRY(run_program(
                region.epilogue, n, c, Source{prefixes(), 1, core_dtype_}));
        }
    }
    if (region.core == RegionCore::PrefixSum) {
        return outcome::success();
    }
    if (region.core == RegionCore::ArgMax ||
        region.core == RegionCore::ArgMin) {
        visit_dtype(core_dtype_, [&]<typename T>() {
            *reinterpret_cast<T *>(accumulator()) =
                static_cast<T>(indices()[0]);
        });
    }
    move_to(c, 0);
    BOOST_OUTCOME_TRY(run_program(region.epilogue, 1, c, core));
    return outcome::success();
}

// Runs the loops outside the region's inner part like an odometer, then the
// inner part at each of their points
Result<void> Executor::run_region(Region const &region)
{
    BOOST_OUTCOME_TRY(bind(region));
    Mode const mode = mode_of(region);
    size_t const n_outer = outer_loops(region);

    std::array<size_t, MAX_RANK> tile_loop{};
    for (size_t l = 0; l < region.n_loops; l++) {
        if (region.loops[l].kind == RegionLoopKind::Tile) {
            tile_loop[region.loops[l].dim] = l;
        }
    }
    std::array<uint64_t, 2 * MAX_RANK> counters{};
    auto const extent = [&](size_t const l) -> uint64_t {
        Loop const &loop = region.loops[l];
        uint64_t const e = region.extents[loop.dim];
        switch (loop.kind) {
        case RegionLoopKind::Whole:
            return e;
        case RegionLoopKind::Tile:
            return (e + loop.tile - 1) / loop.tile;
        case RegionLoopKind::Intra:
            return std::min<uint64_t>(
                loop.tile, e - counters[tile_loop[loop.dim]] * loop.tile);
        }
        MONAD_ABORT();
    };
    for (size_t l = 0; l < n_outer; l++) {
        if (region.extents[region.loops[l].dim] == 0) {
            return outcome::success();
        }
    }

    for (;;) {
        std::array<uint64_t, MAX_RANK> point{};
        for (size_t l = 0; l < n_outer; l++) {
            Loop const &loop = region.loops[l];
            point[loop.dim] += loop.kind == RegionLoopKind::Tile
                                   ? counters[l] * loop.tile
                                   : counters[l];
        }
        for (size_t d = 0; d < region.rank; d++) {
            if (point[d] != index_[d]) {
                move_to(d, point[d]);
            }
        }

        if (mode == Mode::Horizontal) {
            BOOST_OUTCOME_TRY(run_horizontal());
        }
        else {
            Loop const &chunk = region.loops[region.n_loops - 1];
            size_t const x = chunk.dim;
            uint64_t const e = region.extents[x];
            size_t const n =
                chunk.kind == RegionLoopKind::Whole
                    ? e
                    : std::min<uint64_t>(chunk.tile, e - index_[x]);
            if (n > 0) {
                if (mode == Mode::Map) {
                    BOOST_OUTCOME_TRY(
                        run_program(region.epilogue, n, x, Source{}));
                }
                else {
                    BOOST_OUTCOME_TRY(run_vertical(n, x));
                }
            }
        }

        size_t l = n_outer;
        for (; l > 0; l--) {
            if (++counters[l - 1] < extent(l - 1)) {
                break;
            }
            counters[l - 1] = 0;
        }
        if (l == 0) {
            return outcome::success();
        }
    }
}

// Copies the Code and Literal tensors into the arena
Result<void> Executor::load_tensors()
{
    for (uint16_t id = 0; id < header_.n_tensors; id++) {
        TensorFields const fields = tensor_fields(header_, id);
        if (fields.kind == RegionTensorKind::Code) {
            BOOST_OUTCOME_TRY(auto const tensor, read_tensor(header_, id));
            Tensor out{tensor.type, arena_ + tensor.location};
            BOOST_OUTCOME_TRY(load_code_tensor(
                state_,
                header_.reference(tensor.source),
                ByteOrder::LittleEndian,
                out));
        }
        else if (fields.kind == RegionTensorKind::Literal) {
            std::memcpy(
                arena_ + fields.location,
                header_.literals.data() + fields.source,
                fields.count * dtype_size(fields.dtype));
        }
    }
    return outcome::success();
}

Result<RegionOutputs> Executor::run(std::span<uint8_t const> code)
{
    uint64_t start = times_ ? __rdtsc() : 0;
    BOOST_OUTCOME_TRY(load_tensors());
    BOOST_OUTCOME_TRY(auto const n_statements, read_next<uint16_t>(code));
    if (times_) {
        uint64_t const now = __rdtsc();
        times_->loading += now - start;
        start = now;
        if (times_->statements.size() < n_statements) {
            times_->statements.resize(n_statements);
        }
    }
    for (size_t s = 0; s < n_statements; s++) {
        BOOST_OUTCOME_TRY(auto const kind, read_enum<RegionStatement>(code));
        if (kind == RegionStatement::Region) {
            Region region;
            BOOST_OUTCOME_TRY(read_region(code, region));
            BOOST_OUTCOME_TRY(run_region(region));
        }
        else {
            // A Compose statement, which does nothing at run time
            BOOST_OUTCOME_TRY(read_next<uint16_t>(code));
            BOOST_OUTCOME_TRY(auto const n, read_next<uint8_t>(code));
            code = code.subspan(2 * size_t{n});
        }
        if (times_) {
            uint64_t const now = __rdtsc();
            times_->statements[s] += now - start;
            start = now;
        }
    }
    RegionOutputs outputs{};
    BOOST_OUTCOME_TRY(outputs.size, read_next<uint8_t>(code));
    for (size_t i = 0; i < outputs.size; i++) {
        BOOST_OUTCOME_TRY(auto const id, read_next<uint16_t>(code));
        BOOST_OUTCOME_TRY(auto const tensor, read_tensor(header_, id));
        outputs.tensors[i] =
            Tensor{tensor.type, data(tensor_fields(header_, id))};
    }
    return outputs;
}

// Where the scratch starts: after the tensors, if the arena holds both
Result<size_t> scratch_offset(
    std::span<uint8_t> const arena, std::span<Tensor const> const inputs,
    Header const &header)
{
    if (inputs.size() > MAX_GRAPH_INPUTS) {
        return GraphEvalError::ArityError;
    }
    if (header.arena_bytes > ARENA_SIZE) {
        return GraphEvalError::OutOfMemory;
    }
    uint64_t const offset = (header.arena_bytes + TENSOR_DATA_ALIGNMENT - 1) /
                            TENSOR_DATA_ALIGNMENT * TENSOR_DATA_ALIGNMENT;
    uint64_t const end = offset + REGION_SCRATCH_BYTES;
    if (end > ARENA_SIZE || end > arena.size()) {
        return GraphEvalError::OutOfMemory;
    }
    // Inputs are read in place, and must not be overwritten
    auto const begin = reinterpret_cast<uintptr_t>(arena.data());
    for (Tensor const &input : inputs) {
        auto const data = reinterpret_cast<uintptr_t>(input.data());
        uint64_t const size = input.type().size_bytes();
        if (size != 0 && data < begin + end && begin < data + size) {
            return GraphEvalError::InvalidInput;
        }
    }
    return offset;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<RegionOutputs> RegionInterpreter::run(
    std::span<uint8_t> const arena, State &state,
    std::span<Tensor const> const inputs, std::span<uint8_t const> code,
    RegionTimes *const times)
{
    uint64_t const entry = times ? __rdtsc() : 0;
    MONAD_ASSERT(
        reinterpret_cast<uintptr_t>(arena.data()) % TENSOR_DATA_ALIGNMENT == 0);
    BOOST_OUTCOME_TRY(auto const header, read_header(code));
    BOOST_OUTCOME_TRY(auto const offset, scratch_offset(arena, inputs, header));
    uint64_t const validation_start = times ? __rdtsc() : 0;
    Validator validator{header, inputs, &state};
    BOOST_OUTCOME_TRY(validator.validate(code));
    if (times) {
        times->validation += __rdtsc() - validation_start;
    }
    Executor executor{arena, offset, inputs, header, state, times};
    auto result = executor.run(code);
    if (times) {
        times->total += __rdtsc() - entry;
        times->runs++;
    }
    return result;
}

Result<ValidatedRegionCode>
ValidatedRegionCode::validate(std::span<uint8_t const> const code)
{
    std::span<uint8_t const> rest = code;
    BOOST_OUTCOME_TRY(auto const header, read_header(rest));
    Validator validator{header, {}, nullptr};
    BOOST_OUTCOME_TRY(validator.validate(rest));
    return ValidatedRegionCode{code};
}

Result<RegionOutputs> ValidatedRegionCode::run(
    std::span<uint8_t> const arena, State &state,
    std::span<Tensor const> const inputs, RegionTimes *const times) const
{
    uint64_t const entry = times ? __rdtsc() : 0;
    MONAD_ASSERT(
        reinterpret_cast<uintptr_t>(arena.data()) % TENSOR_DATA_ALIGNMENT == 0);
    std::span<uint8_t const> code = code_;
    BOOST_OUTCOME_TRY(auto const header, read_header(code));
    BOOST_OUTCOME_TRY(auto const offset, scratch_offset(arena, inputs, header));
    uint64_t const checks_start = times ? __rdtsc() : 0;
    BOOST_OUTCOME_TRY(check_inputs(header, inputs));
    if (times) {
        times->validation += __rdtsc() - checks_start;
    }
    Executor executor{arena, offset, inputs, header, state, times};
    auto result = executor.run(code);
    if (times) {
        times->total += __rdtsc() - entry;
        times->runs++;
    }
    return result;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
