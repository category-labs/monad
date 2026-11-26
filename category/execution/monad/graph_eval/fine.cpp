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

#include "category/core/assert.h"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include "category/execution/monad/graph_eval/types.hpp"
#include <category/execution/monad/graph_eval/fine.hpp>

#include <array>
#include <optional>
#include <utility>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

[[gnu::always_inline]]
inline Result<Dtype> binop_fn(std::array<Dtype, 2> const &args)
{
    auto const &[x, y] = args;
    if (x != y) {
        return GraphEvalError::TypeError;
    }
    return x;
}

[[gnu::always_inline]]
inline Result<Dtype> cmp_fn(std::array<Dtype, 2> const &args)
{
    auto const &[x, y] = args;
    if (x != y) {
        return GraphEvalError::TypeError;
    }
    return Dtype::uint8;
}

[[gnu::always_inline]]
inline Result<Dtype> qbinop_fn(uint8_t const frac_bits, std::array<Dtype, 2> const &args)
{
    auto const &[x, y] = args;
    if (x != y) {
        return GraphEvalError::TypeError;
    }
    if (frac_bits > 8 * dtype_size(x)) {
        return GraphEvalError::GraphValidationError;
    }
    return x;
}

[[gnu::always_inline]]
inline Result<Dtype> qunop_fn(uint8_t const frac_bits, std::array<Dtype, 1> const &args)
{
    auto const &[x] = args;
    if (frac_bits > 8 * dtype_size(x)) {
        return GraphEvalError::GraphValidationError;
    }
    return x;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

class ScalarValidator
{
    std::span<uint8_t const> code_;
    size_t n_inputs_;
    size_t n_constants_;
    std::array<Dtype, MAX_SCALAR_REGISTERS> register_dtypes_;
    std::array<bool, MAX_SCALAR_REGISTERS> register_initialized_{false};

    template <FineFn Fn>
    Result<Dtype>
    validate_fn(FnParams<Fn> const &, std::array<Dtype, FnArity<Fn>> const &);

    Result<Dtype> read_fn_arg()
    {
        BOOST_OUTCOME_TRY(auto const id, read_next<register_id_t>(code_));
        if (id >= MAX_SCALAR_REGISTERS) {
            return GraphEvalError::GraphValidationError;
        }
        if (!register_initialized_[id]) {
            // Register was read before ever being written to.
            return GraphEvalError::GraphValidationError;
        }
        return register_dtypes_[id];
    }

    template <size_t N>
    [[gnu::always_inline]]
    Result<std::array<Dtype, N>> read_fn_args()
    {
        std::array<Dtype, N> args;
        for (size_t i = 0; i < N; i++) {
            BOOST_OUTCOME_TRY(args[i], read_fn_arg());
        }
        return args;
    }

    // Index of the first general-purpose register.
    size_t first_gp_reg()
    {
        return n_inputs_ + n_constants_;
    }

    [[gnu::always_inline]]
    Result<size_t> read_output_register()
    {
        BOOST_OUTCOME_TRY(auto const reg, read_next<register_id_t>(code_));
        if (reg < first_gp_reg() || reg >= MAX_SCALAR_REGISTERS) {
            return GraphEvalError::GraphValidationError;
        }
        return reg;
    }

    void set_register(size_t const i, Dtype const dtype)
    {
        register_dtypes_[i] = dtype;
        register_initialized_[i] = true;
    }

public:
    ScalarValidator(
        std::span<uint8_t const> const code, size_t const n_inputs,
        std::array<Dtype, MAX_SCALAR_INPUTS> const &input_types)
        : code_(code)
        , n_inputs_(n_inputs)
    {
        MONAD_DEBUG_ASSERT(n_inputs <= MAX_SCALAR_INPUTS);
        for (size_t i = 0; i < n_inputs; i++) {
            set_register(i, input_types[i]);
        }
    }

    Result<std::tuple<std::span<uint8_t const>, Dtype>> validate();
};

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Add>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Add>> const &args)
{
    return binop_fn(args);
}

// FAdd: Add's type
template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::FAdd>(
    std::monostate const &,
    std::array<Dtype, FnArity<FineFn::FAdd>> const &args)
{
    return binop_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Sub>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Sub>> const &args)
{
    return binop_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Mul>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Mul>> const &args)
{
    return binop_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Divc>(
    uint64_t const &denominator,
    std::array<Dtype, FnArity<FineFn::Divc>> const &args)
{
    if (denominator == 0) {
        return GraphEvalError::DivisionByZero;
    }
    return args[0];
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Div>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Div>> const &args)
{
    return binop_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Lt>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Lt>> const &args)
{
    return cmp_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Le>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Le>> const &args)
{
    return cmp_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Eq>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Eq>> const &args)
{
    return cmp_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Where>(
    std::monostate const &,
    std::array<Dtype, FnArity<FineFn::Where>> const &args)
{
    auto const &[cond, x, y] = args;
    if (cond != Dtype::uint8 || x != y) {
        return GraphEvalError::TypeError;
    }
    return x;
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Min>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Min>> const &args)
{
    return binop_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Max>(
    std::monostate const &, std::array<Dtype, FnArity<FineFn::Max>> const &args)
{
    return binop_fn(args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::Saturate>(
    Dtype const &result_dtype,
    std::array<Dtype, FnArity<FineFn::Saturate>> const &)
{
    return result_dtype;
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::QMul>(
    uint8_t const &frac_bits,
    std::array<Dtype, FnArity<FineFn::QMul>> const &args)
{
    return qbinop_fn(frac_bits, args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::QDiv>(
    uint8_t const &frac_bits,
    std::array<Dtype, FnArity<FineFn::QDiv>> const &args)
{
    return qbinop_fn(frac_bits, args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::QExp>(
    uint8_t const &frac_bits,
    std::array<Dtype, FnArity<FineFn::QExp>> const &args)
{
    return qunop_fn(frac_bits, args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::QInvSqrt>(
    uint8_t const &frac_bits,
    std::array<Dtype, FnArity<FineFn::QInvSqrt>> const &args)
{
    return qunop_fn(frac_bits, args);
}

template <>
Result<Dtype> ScalarValidator::validate_fn<FineFn::ISqrt>(
    std::monostate const &,
    std::array<Dtype, FnArity<FineFn::ISqrt>> const &args)
{
    auto const &[x] = args;
    if (dtype_signed(x)) {
        return GraphEvalError::TypeError;
    }
    return x;
}

Result<std::tuple<std::span<uint8_t const>, Dtype>> ScalarValidator::validate()
{
    BOOST_OUTCOME_TRY(n_constants_, read_next<uint8_t>(code_));
    if (n_constants_ + n_inputs_ > MAX_SCALAR_REGISTERS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_constants_; i++) {
        BOOST_OUTCOME_TRY(auto const dtype, read_next<Dtype>(code_));
        set_register(n_inputs_ + i, dtype);
        BOOST_OUTCOME_TRY(read_bytes(code_, dtype_size(dtype)));
    }

    BOOST_OUTCOME_TRY(auto const n_fns, read_next<uint8_t>(code_));
    if (n_fns == 0) {
        return GraphEvalError::GraphValidationError;
    }

    Dtype result_dtype = Dtype::uint8;
    for (size_t i = 0; i < n_fns; i++) {
        BOOST_OUTCOME_TRY(auto const fn, read_next<FineFn>(code_));
        BOOST_OUTCOME_TRY(
            auto const fn_result_dtype,
            visit_fn(fn, [&]<FineFn Fn>() -> Result<Dtype> {
                BOOST_OUTCOME_TRY(
                    auto const params, read_next<FnParams<Fn>>(code_));
                BOOST_OUTCOME_TRY(auto const args, read_fn_args<FnArity<Fn>>());
                // TODO: we're not checking that the output isn't one of the
                // operands
                return validate_fn<Fn>(params, args);
            }));

        // Read the destination register. The last fn has no
        // destination register, and its output will be written
        // directly to the result tensor.
        if (i + 1 < n_fns) {
            BOOST_OUTCOME_TRY(
                auto const output_register, read_output_register());
            set_register(output_register, fn_result_dtype);
        }
        else {
            result_dtype = fn_result_dtype;
        }
    }

    return {code_, result_dtype};
}

class FinecodeValidator
{
    std::span<uint8_t const> code_;
    // Always a multiple of TENSOR_DATA_ALIGNMENT, as is ARENA_SIZE
    size_t memory_usage_ = 0;
    // Set by validate_op for an op whose result needs no memory of its own,
    // a Reshape or a Literal: its location
    std::optional<uint32_t> view_location_;
    Finecode finecode_;

    explicit FinecodeValidator(std::span<uint8_t const> const code)
        : code_(code)
    {
    }

    // Arena memory for a tensor of `type`, rounded up to
    // TENSOR_DATA_ALIGNMENT: its offset. memory_usage_ and ARENA_SIZE are
    // multiples of it, so the rounded size fits if the size does
    Result<uint32_t> allocate(TensorType const &type)
    {
        if (ARENA_SIZE - memory_usage_ < type.size_bytes()) {
            return GraphEvalError::OutOfMemory;
        }
        auto const offset = static_cast<uint32_t>(memory_usage_);
        memory_usage_ += (type.size_bytes() + TENSOR_DATA_ALIGNMENT - 1) &
                         ~(TENSOR_DATA_ALIGNMENT - 1);
        return offset;
    }

    [[gnu::always_inline]]
    Result<TensorType const *> read_op_input()
    {
        BOOST_OUTCOME_TRY(auto const input_id, read_next<node_id_t>(code_));
        if (input_id >= finecode_.tensor_types_.size()) {
            return GraphEvalError::InvalidInput;
        }
        return &finecode_.tensor_types_[input_id];
    }

    template <FineOp Op>
    [[gnu::always_inline]]
    Result<std::array<TensorType const *, OpArity<Op>>> read_op_inputs()
    {
        std::array<TensorType const *, OpArity<Op>> inputs;
        for (size_t i = 0; i < OpArity<Op>; i++) {
            BOOST_OUTCOME_TRY(inputs[i], read_op_input());
        }
        return inputs;
    }

    template <FineOp Op>
    Result<TensorType> validate_op(OpParams<Op> const &);

    Result<TensorType> validate_dim_reduce(uint8_t const &dim)
    {
        BOOST_OUTCOME_TRY(auto const x, read_op_input());
        if (dim >= x->shape().rank()) {
            return GraphEvalError::RankError;
        }
        if (x->shape().dimensions()[dim] == 0) {
            return GraphEvalError::ShapeError;
        }
        auto dimensions = x->shape().dimensions();
        dimensions[dim] = 1;
        BOOST_OUTCOME_TRY(
            auto const shape, Shape::checked(x->shape().rank(), dimensions));
        return TensorType::checked(x->dtype(), shape);
    }

    // ArgMin's and ArgMax's checks and shape are ReduceMax's, with Uint16
    // elements whatever the input's dtype: each is an index along axis,
    // below the input's dimension there, which is at most 65535
    Result<TensorType> validate_arg_reduce(uint8_t const axis)
    {
        BOOST_OUTCOME_TRY(auto const reduced, validate_dim_reduce(axis));
        return TensorType::checked(Dtype::uint16, reduced.shape());
    }

    Result<void> validate();

public:
    static Finecode validate(std::span<uint8_t const> const code)
    {
        FinecodeValidator validator{code};
        auto const validation_result = validator.validate();
        if (!validation_result.has_error()) {
            validator.finecode_.validation_result_ = GraphEvalError::Success;
        }
        else if (
            validation_result.error().domain() ==
            system_error2::quick_status_code_from_enum_code<
                GraphEvalError>::domain_type::get()) {
            validator.finecode_.validation_result_ =
                static_cast<GraphEvalError>(validation_result.error().value());
        }
        else {
            validator.finecode_.validation_result_ =
                GraphEvalError::InternalError;
        }

        return std::move(validator.finecode_);
    }
};

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::Scalar>(Shape const &output_shape)
{
    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_));
    if (n_inputs > MAX_SCALAR_INPUTS) {
        return GraphEvalError::ArityError;
    }
    std::array<Dtype, MAX_SCALAR_INPUTS> input_dtypes;
    for (size_t i = 0; i < n_inputs; i++) {
        BOOST_OUTCOME_TRY(auto const tensor_type, read_op_input());
        // TODO: store the broadcasting loops to avoid recomputing them
        BOOST_OUTCOME_TRY(tensor_type->shape().broadcast_to(output_shape));
        input_dtypes[i] = tensor_type->dtype();
    }
    ScalarValidator validator{code_, n_inputs, input_dtypes};
    BOOST_OUTCOME_TRY(auto const result, validator.validate());
    auto const &[code, dtype] = result;
    code_ = code;

    return TensorType::checked(dtype, output_shape);
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::Literal>(TensorType const &ty)
{
    if (code_.size() < ty.size_bytes()) {
        return GraphEvalError::GraphValidationError;
    }
    // The data stays in the code, unaligned, where the interpreter reads it;
    // its location is an offset from the start of the ops
    auto const offset = static_cast<size_t>(code_.data() - finecode_.ops_);
    if (offset >= FINE_CODE_LOCATION) {
        return GraphEvalError::GraphValidationError;
    }
    view_location_ = static_cast<uint32_t>(offset) | FINE_CODE_LOCATION;
    code_ = code_.subspan(ty.size_bytes());
    return ty;
}

template <>
Result<TensorType> FinecodeValidator::validate_op<FineOp::TensorRef>(
    std::tuple<TensorType, Address, uint32_t> const &params)
{
    auto const &[ty, addr, offset] = params;
    return ty;
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::Reshape>(Shape const &shape)
{
    BOOST_OUTCOME_TRY(auto const &[input], read_op_inputs<FineOp::Reshape>());
    if (input->shape().size() != shape.size()) {
        return GraphEvalError::ShapeError;
    }
    // A view of its input's data
    view_location_ = finecode_.node_locations_[static_cast<size_t>(
        input - finecode_.tensor_types_.data())];
    return TensorType::checked(input->dtype(), shape);
}

template <>
Result<TensorType> FinecodeValidator::validate_op<FineOp::Transpose>(
    std::tuple<uint8_t, uint8_t> const &params)
{
    auto const &[axis0, axis1] = params;
    BOOST_OUTCOME_TRY(auto const &[x], read_op_inputs<FineOp::Transpose>());
    // A rank-0 x has no axis, so it fails here
    if (axis0 >= x->shape().rank() || axis1 >= x->shape().rank()) {
        return GraphEvalError::RankError;
    }
    std::array<uint16_t, MAX_RANK> dimensions = x->shape().dimensions();
    std::swap(dimensions[axis0], dimensions[axis1]);
    BOOST_OUTCOME_TRY(
        auto const shape, Shape::checked(x->shape().rank(), dimensions));
    return TensorType::checked(x->dtype(), shape);
}

template <>
Result<TensorType> FinecodeValidator::validate_op<FineOp::Concat>(
    std::tuple<uint8_t, uint8_t> const &params)
{
    auto const &[axis, n_inputs] = params;
    if (n_inputs < 2 || n_inputs > MAX_CONCAT_INPUTS) {
        return GraphEvalError::ArityError;
    }
    // Each input after the first, x, must have x's dtype, rank and dimensions,
    // except along axis
    BOOST_OUTCOME_TRY(auto const x, read_op_input());
    // A rank-0 x has no axis, so it fails here
    if (axis >= x->shape().rank()) {
        return GraphEvalError::RankError;
    }
    // At most MAX_CONCAT_INPUTS lengths of up to 65535 each, so no overflow
    uint32_t concat_len = x->shape().dimensions()[axis];
    for (size_t i = 1; i < n_inputs; i++) {
        BOOST_OUTCOME_TRY(auto const y, read_op_input());
        if (x->dtype() != y->dtype()) {
            return GraphEvalError::TypeError;
        }
        if (x->shape().rank() != y->shape().rank()) {
            return GraphEvalError::RankError;
        }
        for (size_t d = 0; d < x->shape().rank(); d++) {
            if (d != axis &&
                x->shape().dimensions()[d] != y->shape().dimensions()[d]) {
                return GraphEvalError::ShapeError;
            }
        }
        concat_len += uint32_t{y->shape().dimensions()[axis]};
    }
    // The output's length along axis, which the MIP's MAX_DIM, 65535, bounds
    if (concat_len > std::numeric_limits<uint16_t>::max()) {
        return GraphEvalError::ShapeError;
    }

    std::array<uint16_t, MAX_RANK> dimensions = x->shape().dimensions();
    dimensions[axis] = static_cast<uint16_t>(concat_len);
    BOOST_OUTCOME_TRY(
        auto const shape, Shape::checked(x->shape().rank(), dimensions));
    return TensorType::checked(x->dtype(), shape);
}

template <>
Result<TensorType> FinecodeValidator::validate_op<FineOp::QMatMul>(
    std::tuple<uint8_t, Dtype> const &params)
{
    auto const &[frac_bits, out_dtype] = params;
    // Up to 64, whatever out_dtype's width
    if (frac_bits > 64) {
        return GraphEvalError::GraphValidationError;
    }
    BOOST_OUTCOME_TRY(auto const inputs, read_op_inputs<FineOp::QMatMul>());
    auto const &[x, y] = inputs;
    if (x->shape().rank() != 2 || y->shape().rank() != 2) {
        return GraphEvalError::RankError;
    }
    // x is [m, k] and y is [n, k]; the output is [m, n]
    if (x->shape().dimensions()[1] != y->shape().dimensions()[1]) {
        return GraphEvalError::ShapeError;
    }
    if (x->dtype() != y->dtype()) {
        return GraphEvalError::TypeError;
    }
    std::array<uint16_t, MAX_RANK> dimensions{};
    dimensions[0] = x->shape().dimensions()[0];
    dimensions[1] = y->shape().dimensions()[0];
    BOOST_OUTCOME_TRY(auto const shape, Shape::checked(2, dimensions));
    BOOST_OUTCOME_TRY(auto const type, TensorType::checked(out_dtype, shape));
    return type;
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::CumSum>(uint8_t const &dim)
{
    BOOST_OUTCOME_TRY(auto const &[x], read_op_inputs<FineOp::CumSum>());
    if (dim >= x->shape().rank()) {
        return GraphEvalError::RankError;
    }
    return *x;
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::ArgMin>(uint8_t const &axis)
{
    return validate_arg_reduce(axis);
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::ArgMax>(uint8_t const &axis)
{
    return validate_arg_reduce(axis);
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::ReduceSum>(uint8_t const &dim)
{
    return validate_dim_reduce(dim);
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::ReduceMax>(uint8_t const &dim)
{
    return validate_dim_reduce(dim);
}

template <>
Result<TensorType>
FinecodeValidator::validate_op<FineOp::Gather>(uint8_t const &dim)
{
    BOOST_OUTCOME_TRY(auto const inputs, read_op_inputs<FineOp::Gather>());
    auto const &[x, idx] = inputs;
    if (dim >= x->shape().rank()) {
        return GraphEvalError::RankError;
    }
    auto const output_rank =
        size_t{x->shape().rank()} - uint8_t{1} + idx->shape().rank();
    if (output_rank > MAX_RANK) {
        return GraphEvalError::RankError;
    }
    auto const rank = static_cast<uint8_t>(output_rank);
    std::array<uint16_t, MAX_RANK> dimensions{};
    for (size_t i = 0; i < dim; i++) {
        dimensions[i] = x->shape().dimensions()[i];
    }
    for (size_t j = 0; j < idx->shape().rank(); j++) {
        dimensions[dim + j] = idx->shape().dimensions()[j];
    }
    for (size_t i = dim + 1; i < x->shape().rank(); i++) {
        dimensions[idx->shape().rank() + i - 1] = x->shape().dimensions()[i];
    }
    BOOST_OUTCOME_TRY(auto const shape, Shape::checked(rank, dimensions));
    return TensorType::checked(x->dtype(), shape);
}

Result<void> FinecodeValidator::validate()
{
    BOOST_OUTCOME_TRY(expect_next<GRAPH_MAGIC>(code_));
    // V1 is the only currently supported version.
    BOOST_OUTCOME_TRY(expect_next<FineVersion::V1>(code_));
    BOOST_OUTCOME_TRY(finecode_.n_inputs_, read_next<uint8_t>(code_));
    if (finecode_.n_inputs_ > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }

    for (size_t i = 0; i < finecode_.n_inputs_; i++) {
        BOOST_OUTCOME_TRY(auto const input_ty, read_next<TensorType>(code_));
        finecode_.tensor_types_.push_back(input_ty);
        BOOST_OUTCOME_TRY(auto const location, allocate(input_ty));
        finecode_.node_locations_.push_back(location);
    }

    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code_));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(auto const output_id, read_next<node_id_t>(code_));
        finecode_.output_ids_.push_back(output_id);
    }

    BOOST_OUTCOME_TRY(finecode_.n_ops_, read_next<uint16_t>(code_));
    if (finecode_.n_ops_ > MAX_GRAPH_OPS) {
        return GraphEvalError::GraphValidationError;
    }

    for (auto const output_id : finecode_.output_ids_) {
        if (output_id >= finecode_.n_inputs_ + finecode_.n_ops_) {
            return GraphEvalError::GraphValidationError;
        }
    }

    finecode_.ops_ = code_.data();

    for (size_t i = 0; i < finecode_.n_ops_; i++) {
        BOOST_OUTCOME_TRY(auto const opcode, read_next<FineOp>(code_));
        BOOST_OUTCOME_TRY(visit_op(opcode, [&]<FineOp Op>() -> Result<void> {
            BOOST_OUTCOME_TRY(
                auto const params, read_next<OpParams<Op>>(code_));
            view_location_.reset();
            BOOST_OUTCOME_TRY(auto const result_type, validate_op<Op>(params));
            if (view_location_) {
                finecode_.node_locations_.push_back(*view_location_);
            }
            else {
                BOOST_OUTCOME_TRY(auto const location, allocate(result_type));
                finecode_.node_locations_.push_back(location);
            }
            finecode_.tensor_types_.push_back(result_type);
            return outcome::success();
        }));
    }

    if (!code_.empty()) {
        return GraphEvalError::GraphValidationError;
    }
    return outcome::success();
}

Finecode validate(std::span<uint8_t const> code)
{
    return FinecodeValidator::validate(code);
}

MONAD_GRAPH_EVAL_NAMESPACE_END
