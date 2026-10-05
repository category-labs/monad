#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include <category/core/math.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>

#include <algorithm>
#include <array>
#include <chrono>
#include <concepts>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iostream>
#include <limits>
#include <span>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN
template <typename T>
Result<T> read_next(std::span<uint8_t const> &);

template <typename T>
    requires(std::integral<T>)
[[gnu::always_inline]]
inline Result<T> read_next(std::span<uint8_t const> &input)
{
    if (input.size() < sizeof(T)) {
        return GraphEvalError::GraphValidationError;
    }

    std::remove_cv_t<T> result{};
    std::memcpy(&result, input.data(), sizeof(result));
    input = input.subspan(sizeof(T));
    return result;
}

// Rejects bytes that don't name a Dtype, so the result is always safe to pass
// to dtype_size, which aborts on anything else
template <>
[[gnu::always_inline]]
inline Result<Dtype> read_next<Dtype>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<Dtype>>(input));
    if (id >
        static_cast<std::underlying_type_t<Dtype>>(Dtype::Last_valid_dtype)) {
        return GraphEvalError::TypeError;
    }
    return static_cast<Dtype>(id);
}

// Parameters of an op that takes none, encoded as zero bytes
template <>
[[gnu::always_inline]]
inline Result<std::monostate>
read_next<std::monostate>(std::span<uint8_t const> &)
{
    return std::monostate{};
}

// Rank (uint8), then `rank` dimensions (uint16 each). Rejects shapes whose
// element count overflows uint64, so Shape::size() is exact
template <>
[[gnu::always_inline]]
inline Result<Shape> read_next<Shape>(std::span<uint8_t const> &input)
{
    Shape shape{};
    BOOST_OUTCOME_TRY(shape.rank, read_next<uint8_t>(input));
    if (shape.rank > shape.dimensions.size()) {
        return GraphEvalError::RankError;
    }

    uint64_t size = 1;
    for (size_t i = 0; i < shape.rank; i++) {
        BOOST_OUTCOME_TRY(shape.dimensions[i], read_next<uint16_t>(input));
        if (MONAD_UNLIKELY(
                __builtin_mul_overflow(size, shape.dimensions[i], &size))) {
            return GraphEvalError::ShapeError;
        }
    }
    return shape;
}

template <typename T>
inline constexpr bool is_tuple_v = false;

template <typename... Ts>
inline constexpr bool is_tuple_v<std::tuple<Ts...>> = true;

// Reads the elements in order. Function templates can't be partially
// specialized, so tuples get an overload constrained to them instead
template <typename T>
    requires(is_tuple_v<T>)
[[gnu::always_inline]]
inline Result<T> read_next(std::span<uint8_t const> &input)
{
    if constexpr (std::tuple_size_v<T> == 0) {
        return T{};
    }
    else {
        return [&]<typename Head, typename... Tail>(
                   std::type_identity<std::tuple<Head, Tail...>>) -> Result<T> {
            BOOST_OUTCOME_TRY(auto head, read_next<Head>(input));
            BOOST_OUTCOME_TRY(auto tail, read_next<std::tuple<Tail...>>(input));
            return std::tuple_cat(
                std::tuple<Head>{std::move(head)}, std::move(tail));
        }(std::type_identity<T>{});
    }
}

// Consumes the next `size` bytes of `input`
Result<std::span<uint8_t const>>
read_bytes(std::span<uint8_t const> &input, uint64_t const size)
{
    if (input.size() < size) {
        return GraphEvalError::GraphValidationError;
    }
    auto const bytes = input.first(static_cast<size_t>(size));
    input = input.subspan(static_cast<size_t>(size));
    return bytes;
}

// Literal parameters: a tensor header, then the data, packed row-major in the
// same byte order as the rest of the graphcode. The data's length depends on
// the header, so unlike other tuples this one isn't read element by element.
// Reading the data here, before the op allocates anything, means a literal
// can't claim more data than the graphcode holds and get that much memory
// allocated
template <>
[[gnu::always_inline]]
inline Result<std::tuple<Dtype, Shape, std::span<uint8_t const>>>
read_next<std::tuple<Dtype, Shape, std::span<uint8_t const>>>(
    std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const header, read_next<std::tuple<Dtype, Shape>>(input));
    auto const &[dtype, shape] = header;

    uint64_t size;
    if (MONAD_UNLIKELY(
            __builtin_mul_overflow(dtype_size(dtype), shape.size(), &size))) {
        return GraphEvalError::ShapeError;
    }
    BOOST_OUTCOME_TRY(auto const data, read_bytes(input, size));
    return std::tuple{dtype, shape, data};
}

// A loop rather than std::equal, which GCC makes a call to memcmp
bool same_shape(Shape const &a, Shape const &b)
{
    if (a.rank != b.rank) {
        return false;
    }
    for (size_t d = 0; d < a.rank; d++) {
        if (a.dimensions[d] != b.dimensions[d]) {
            return false;
        }
    }
    return true;
}

// The loops of an element-wise op over N operands broadcast together as numpy
// broadcasts them: shapes are matched from their last dimensions, and each of
// the output's dimensions is the operands' common size, an operand being
// repeated along any dimension where its size is 1 or it has none
template <size_t N>
struct BroadcastLoops
{
    Shape shape; // The output's

    // The loops, innermost first: the output's dimensions without those of
    // size 1, merged wherever every operand steps through adjacent ones
    // contiguously, so the innermost loop is as long as possible. Each loop's
    // length, and each operand's stride along it in elements, 0 where the
    // operand is repeated.
    size_t rank;
    std::array<uint64_t, 8> lengths;
    std::array<std::array<uint64_t, 8>, N> strides;
};

template <size_t N>
Result<BroadcastLoops<N>> broadcast(std::array<Shape, N> const &shapes)
{
    // Not zero-filled, since GCC does that with a rep stosq, which costs about
    // a third of a small call; each of the loops' lengths and strides is
    // written before it's read
    BroadcastLoops<N> loops;
    loops.shape = Shape{};
    loops.rank = 0;
    Shape &shape = loops.shape;
    for (Shape const &operand : shapes) {
        shape.rank = std::max(shape.rank, operand.rank);
    }
    std::fill_n(shape.dimensions.begin(), shape.rank, uint16_t{1});

    // Each operand's stride along each of the output's dimensions
    std::array<std::array<uint64_t, 8>, N> strides{};
    for (size_t k = 0; k < N; k++) {
        Shape const &operand = shapes[k];
        uint64_t stride = 1;
        for (size_t i = operand.rank; i-- > 0;) {
            size_t const d = shape.rank - operand.rank + i;
            uint16_t const size = operand.dimensions[i];
            if (size != 1) {
                if (shape.dimensions[d] != 1 && shape.dimensions[d] != size) {
                    return GraphEvalError::ShapeError;
                }
                shape.dimensions[d] = size;
                strides[k][d] = stride;
            }
            stride *= size;
        }
    }

    for (size_t d = shape.rank; d-- > 0;) {
        uint64_t const length = shape.dimensions[d];
        if (length == 1) {
            continue;
        }
        bool merges = loops.rank > 0;
        for (size_t k = 0; k < N && merges; k++) {
            size_t const inner = loops.rank - 1;
            merges =
                strides[k][d] == loops.strides[k][inner] * loops.lengths[inner];
        }
        if (merges) {
            loops.lengths[loops.rank - 1] *= length;
        }
        else {
            loops.lengths[loops.rank] = length;
            for (size_t k = 0; k < N; k++) {
                loops.strides[k][loops.rank] = strides[k][d];
            }
            loops.rank++;
        }
    }
    return loops;
}

// Calls f(offsets, start, length, strides) for each run of the innermost of
// `loops`, in the output's order: each operand's offset at the start of the
// run, where it starts in the output, its length, and each operand's stride
// along it. Those strides are the same for every run, and always 0 or 1, since
// an operand that isn't repeated along the innermost loop is contiguous along
// it.
template <size_t N, typename F>
void for_each_run(BroadcastLoops<N> const &loops, F const &f)
{
    std::array<uint64_t, N> offsets{};
    if (loops.rank == 0) {
        f(offsets, 0, 1, std::array<uint64_t, N>{});
        return;
    }
    for (size_t d = 0; d < loops.rank; d++) {
        if (loops.lengths[d] == 0) {
            return;
        }
    }

    std::array<uint64_t, N> inner_strides{};
    for (size_t k = 0; k < N; k++) {
        inner_strides[k] = loops.strides[k][0];
    }
    uint64_t const length = loops.lengths[0];
    // The position in the outer loops, advanced like an odometer
    std::array<uint64_t, 8> index{};
    for (uint64_t start = 0;; start += length) {
        f(offsets, start, length, inner_strides);
        size_t d;
        for (d = 1; d < loops.rank; d++) {
            for (size_t k = 0; k < N; k++) {
                offsets[k] += loops.strides[k][d];
            }
            if (++index[d] < loops.lengths[d]) {
                break;
            }
            for (size_t k = 0; k < N; k++) {
                offsets[k] -= loops.strides[k][d] * loops.lengths[d];
            }
            index[d] = 0;
        }
        if (d == loops.rank) {
            return;
        }
    }
}

// The *_run functions compute one run from for_each_run. Their pointers are
// restrict, since an op's output is a fresh allocation and so never overlaps
// its inputs, which lets GCC vectorize the loops; they're parameters because
// GCC ignores restrict on local variables. Each stride is 1 or, where the
// operand is repeated along the run, 0, and there's a loop for each pattern,
// with a repeated operand read once, so that GCC knows how each operand is
// stepped through. Only a run of a single element, from operands with no
// dimensions, has every operand repeated.

// Applies F to a run of xs and ys, into outs
template <typename F, typename T, typename Out>
[[gnu::always_inline]]
inline void binary_run(
    T const *__restrict const xs, T const *__restrict const ys,
    Out *__restrict const outs, uint64_t const length, uint64_t const x_stride,
    uint64_t const y_stride)
{
    if (x_stride == 1 && y_stride == 1) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(xs[i], ys[i]));
        }
    }
    else if (x_stride == 1) {
        T const y = ys[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(xs[i], y));
        }
    }
    else if (y_stride == 1) {
        T const x = xs[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(x, ys[i]));
        }
    }
    else {
        Out const result = static_cast<Out>(F{}(xs[0], ys[0]));
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = result;
        }
    }
}

// Copies a run of xs into outs
template <typename T>
[[gnu::always_inline]]
inline void copy_run(
    T const *__restrict const xs, T *__restrict const outs,
    uint64_t const length, uint64_t const x_stride)
{
    if (x_stride == 1) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = xs[i];
        }
    }
    else {
        T const x = xs[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = x;
        }
    }
}

// Picks each element of a run from xs where `conditions` is nonzero, else from
// ys, into outs. A repeated condition picks the same operand for the whole run,
// so that's a copy of it.
template <typename T>
[[gnu::always_inline]]
inline void where_run(
    uint8_t const *__restrict const conditions, T const *__restrict const xs,
    T const *__restrict const ys, T *__restrict const outs,
    uint64_t const length, uint64_t const condition_stride,
    uint64_t const x_stride, uint64_t const y_stride)
{
    if (condition_stride == 0) {
        if (conditions[0] != 0) {
            copy_run(xs, outs, length, x_stride);
        }
        else {
            copy_run(ys, outs, length, y_stride);
        }
    }
    else if (x_stride == 1 && y_stride == 1) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = conditions[i] != 0 ? xs[i] : ys[i];
        }
    }
    else if (x_stride == 1) {
        T const y = ys[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = conditions[i] != 0 ? xs[i] : y;
        }
    }
    else if (y_stride == 1) {
        T const x = xs[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = conditions[i] != 0 ? x : ys[i];
        }
    }
    else {
        T const x = xs[0];
        T const y = ys[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = conditions[i] != 0 ? x : y;
        }
    }
}

// Converts to To, clamping values outside its range to the nearest bound
template <typename To, typename From>
To saturate_cast(From const value)
{
    if (std::cmp_less(value, std::numeric_limits<To>::min())) {
        return std::numeric_limits<To>::min();
    }
    if (std::cmp_greater(value, std::numeric_limits<To>::max())) {
        return std::numeric_limits<To>::max();
    }
    return static_cast<To>(value);
}

// Two's complement wrapping arithmetic, without the UB of signed overflow
struct WrappingAdd
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        T result{};
        (void)__builtin_add_overflow(a, b, &result);
        return result;
    }
};

struct WrappingSub
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        T result{};
        (void)__builtin_sub_overflow(a, b, &result);
        return result;
    }
};

// The memory for the tensors that evaluations on a thread compute, handed out
// by bumping `used_` and reset by each evaluation. It's kept for the thread's
// lifetime, so its pages are faulted in once rather than for every tensor.
class Arena
{
    uint8_t *const data_;
    uint64_t used_ = 0;

public:
    Arena()
        : data_(static_cast<uint8_t *>(
              std::aligned_alloc(IREE_ALIGNMENT, ARENA_SIZE)))
    {
        MONAD_ASSERT(data_ != nullptr);
    }

    ~Arena()
    {
        std::free(data_);
    }

    Arena(Arena const &) = delete;
    Arena &operator=(Arena const &) = delete;

    void reset()
    {
        used_ = 0;
    }

    // `size` bytes aligned to IREE_ALIGNMENT, or null if there isn't room
    uint8_t *allocate(uint64_t const size)
    {
        // ARENA_SIZE and used_ are multiples of the alignment, so this also
        // leaves room for the padding
        if (size > ARENA_SIZE - used_) {
            return nullptr;
        }
        uint8_t *const data = data_ + used_;
        used_ += round_up(size, IREE_ALIGNMENT);
        return data;
    }
};

Arena &thread_arena()
{
    thread_local Arena arena;
    return arena;
}

// Benchmarking: set to print how long each op takes
constexpr bool PRINT_NODE_TIMES = true;

// Benchmarking: how long the op that computed `node` took
void print_node_time(
    size_t const node, Op const op, Tensor const &tensor,
    std::chrono::steady_clock::duration const elapsed)
{
    std::cerr << "  node " << node << " " << op_name(op) << " [";
    for (size_t i = 0; i < tensor.rank(); i++) {
        std::cerr << (i == 0 ? "" : ", ") << tensor.dimensions()[i];
    }
    std::cerr << "]: " << std::chrono::duration<double, std::micro>(elapsed)
              << std::endl;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void> Interpreter::check_magic_number()
{
    BOOST_OUTCOME_TRY(auto const magic, read_next<uint16_t>(graphcode_));
    if (magic != 0x7ffe) {
        return GraphEvalError::GraphValidationError;
    }
    return outcome::success();
}

Result<void> Interpreter::check_inputs()
{
    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(graphcode_));
    if (n_inputs > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    if (n_inputs != node_values_.size()) {
        return GraphEvalError::ArityError;
    }

    for (auto i = 0; i < n_inputs; i++) {
        auto const &input = node_values_[static_cast<size_t>(i)];

        BOOST_OUTCOME_TRY(auto const dtype, read_next<uint8_t>(graphcode_));
        if (dtype != static_cast<uint8_t>(input.dtype())) {
            return GraphEvalError::TypeError;
        }

        BOOST_OUTCOME_TRY(auto const rank, read_next<uint8_t>(graphcode_));
        if (rank != input.rank()) {
            return GraphEvalError::RankError;
        }

        for (auto j = 0; j < rank; j++) {
            BOOST_OUTCOME_TRY(auto const d_j, read_next<uint16_t>(graphcode_));
            if (d_j != input.dimensions()[static_cast<size_t>(j)]) {
                return GraphEvalError::ShapeError;
            }
        }
    }

    return outcome::success();
}

// The data comes from the thread's arena, so it's only valid until the next
// evaluation on the thread starts
Result<Tensor>
Interpreter::allocate_tensor(Dtype const dtype, Shape const &shape)
{
    uint64_t size = dtype_size(dtype);
    for (size_t i = 0; i < shape.rank; i++) {
        if (MONAD_UNLIKELY(
                __builtin_mul_overflow(size, shape.dimensions[i], &size))) {
            return GraphEvalError::ShapeError;
        }
    }

    // TODO: charge gas for the size
    uint8_t *const data = thread_arena().allocate(size);
    if (MONAD_UNLIKELY(data == nullptr)) {
        return GraphEvalError::OutOfMemory;
    }
    return Tensor(dtype, shape, data);
}

// Base for graph ops. After its opcode, an op's graphcode holds its
// parameters, as read by `read_next<Parameters>`, then one uint16 node index
// per input. A node index names a graph input or an earlier op's result, so
// inputs can only refer backwards. A derived op computes its result from the
// loaded parameters and inputs in `evaluate`, allocating it through
// `interpreter_`. An op without parameters uses std::monostate.
template <typename Parameters, typename... Inputs>
    requires(std::convertible_to<Tensor const &, Inputs> && ...)
struct GraphOp
{
    explicit GraphOp(Interpreter &interpreter)
        : interpreter_(interpreter)
    {
    }

    virtual Result<Tensor> evaluate(Parameters params, Inputs... inputs) = 0;

    Result<Tensor> operator()(
        std::span<uint8_t const> &graphcode,
        std::vector<Tensor> const &node_values)
    {
        BOOST_OUTCOME_TRY(auto const params, read_next<Parameters>(graphcode));

        std::array<uint16_t, sizeof...(Inputs)> node_ids{};
        for (auto &node_id : node_ids) {
            BOOST_OUTCOME_TRY(node_id, read_next<uint16_t>(graphcode));
            if (node_id >= node_values.size()) {
                return GraphEvalError::GraphValidationError;
            }
        }

        return [&]<size_t... I>(std::index_sequence<I...>) {
            return evaluate(params, node_values[node_ids[I]]...);
        }(std::index_sequence_for<Inputs...>{});
    }

protected:
    ~GraphOp() = default;

    Interpreter &interpreter_;
};

// Literal: a constant tensor, copied out of the graphcode
struct LiteralOp final
    : GraphOp<std::tuple<Dtype, Shape, std::span<uint8_t const>>>
{
    using GraphOp::GraphOp;

    Result<Tensor>
    evaluate(std::tuple<Dtype, Shape, std::span<uint8_t const>> const params)
        override
    {
        auto const &[dtype, shape, data] = params;
        BOOST_OUTCOME_TRY(
            auto const tensor, interpreter_.allocate_tensor(dtype, shape));
        std::memcpy(tensor.data(), data.data(), data.size());
        return tensor;
    }
};

// Applies F element by element to two tensors of the same dtype, with their
// shapes broadcast together. The output has the broadcast shape, and the dtype
// of what F returns, with bool stored as uint8 0/1.
template <typename F>
struct BinaryElementwiseOp final
    : GraphOp<std::monostate, Tensor const &, Tensor const &>
{
    using GraphOp::GraphOp;

    Result<Tensor>
    evaluate(std::monostate, Tensor const &x, Tensor const &y) override
    {
        if (x.dtype() != y.dtype()) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const loops, broadcast<2>({x.shape(), y.shape()}));

        return visit_dtype(x.dtype(), [&]<typename T>() -> Result<Tensor> {
            using R = std::invoke_result_t<F, T, T>;
            using Out = std::conditional_t<std::same_as<R, bool>, uint8_t, R>;
            BOOST_OUTCOME_TRY(
                auto const out,
                interpreter_.allocate_tensor(dtype_of<Out>(), loops.shape));
            T const *const xs = x.elements<T const>().data();
            T const *const ys = y.elements<T const>().data();
            Out *const outs = out.template elements<Out>().data();
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    binary_run<F>(
                        xs + offsets[0],
                        ys + offsets[1],
                        outs + start,
                        length,
                        strides[0],
                        strides[1]);
                });
            return out;
        });
    }
};

using AddOp = BinaryElementwiseOp<WrappingAdd>;
using SubOp = BinaryElementwiseOp<WrappingSub>;

using GreaterOp = BinaryElementwiseOp<std::greater<>>;

using GeOp = BinaryElementwiseOp<std::greater_equal<>>;
using EqualOp = BinaryElementwiseOp<std::equal_to<>>;

// Reshape: the input's elements under a new shape with the same element count.
// The result shares the input's data, which is safe while tensors are never
// written after they're produced
struct ReshapeOp final : GraphOp<Shape, Tensor const &>
{
    using GraphOp::GraphOp;

    Result<Tensor> evaluate(Shape const shape, Tensor const &x) override
    {
        if (shape.size() != x.shape().size()) {
            return GraphEvalError::ShapeError;
        }
        return Tensor(x.dtype(), shape, x.data());
    }
};

// Where: each element from x where the condition is nonzero, else from y, with
// the three shapes broadcast together. The condition is uint8, as comparisons
// return.
struct WhereOp final
    : GraphOp<std::monostate, Tensor const &, Tensor const &, Tensor const &>
{
    using GraphOp::GraphOp;

    Result<Tensor> evaluate(
        std::monostate, Tensor const &condition, Tensor const &x,
        Tensor const &y) override
    {
        if (condition.dtype() != Dtype::uint8 || x.dtype() != y.dtype()) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<3>({condition.shape(), x.shape(), y.shape()}));

        BOOST_OUTCOME_TRY(
            auto const out,
            interpreter_.allocate_tensor(x.dtype(), loops.shape));
        visit_dtype(x.dtype(), [&]<typename T>() {
            uint8_t const *const conditions =
                condition.elements<uint8_t const>().data();
            T const *const xs = x.elements<T const>().data();
            T const *const ys = y.elements<T const>().data();
            T *const outs = out.elements<T>().data();
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    where_run(
                        conditions + offsets[0],
                        xs + offsets[1],
                        ys + offsets[2],
                        outs + start,
                        length,
                        strides[0],
                        strides[1],
                        strides[2]);
                });
        });
        return out;
    }
};

// Saturate: converts to the dtype given as its parameter, clamping values
// outside that dtype's range to the nearest bound
struct SaturateOp final : GraphOp<Dtype, Tensor const &>
{
    using GraphOp::GraphOp;

    Result<Tensor> evaluate(Dtype const dtype, Tensor const &x) override
    {
        BOOST_OUTCOME_TRY(
            auto const out, interpreter_.allocate_tensor(dtype, x.shape()));
        visit_dtype(x.dtype(), [&]<typename From>() {
            visit_dtype(dtype, [&]<typename To>() {
                auto const xs = x.elements<From const>();
                auto const outs = out.elements<To>();
                for (size_t i = 0; i < outs.size(); i++) {
                    outs[i] = saturate_cast<To>(xs[i]);
                }
            });
        });
        return out;
    }
};

// Expand: broadcasts the input to the shape given as its parameter, as
// numpy.broadcast_to does. The input's dimensions are matched against the
// shape's last ones, and each must equal its counterpart or be 1, in which case
// the input is repeated along it. Element-wise ops broadcast their operands
// themselves, so this is only needed for a broadcast tensor on its own.
struct ExpandOp final : GraphOp<Shape, Tensor const &>
{
    using GraphOp::GraphOp;

    Result<Tensor> evaluate(Shape const shape, Tensor const &x) override
    {
        if (x.rank() > shape.rank) {
            return GraphEvalError::RankError;
        }
        // Broadcasting the input against the shape gives back the shape
        // exactly when each of the input's dimensions matches it or is 1
        BOOST_OUTCOME_TRY(auto const loops, broadcast<2>({shape, x.shape()}));
        if (!same_shape(loops.shape, shape)) {
            return GraphEvalError::ShapeError;
        }

        BOOST_OUTCOME_TRY(
            auto const out, interpreter_.allocate_tensor(x.dtype(), shape));
        visit_dtype(x.dtype(), [&]<typename T>() {
            T const *const xs = x.elements<T const>().data();
            T *const outs = out.elements<T>().data();
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    copy_run(xs + offsets[1], outs + start, length, strides[1]);
                });
        });
        return out;
    }
};

// CumSum: running sums along the axis given as its parameter, inclusive and in
// increasing index order, wrapping on overflow like Add
struct CumSumOp final : GraphOp<uint8_t, Tensor const &>
{
    using GraphOp::GraphOp;

    Result<Tensor> evaluate(uint8_t const axis, Tensor const &x) override
    {
        if (axis >= x.rank()) {
            return GraphEvalError::RankError;
        }

        // The input as `outer` blocks of `length` rows of `inner` elements,
        // with the axis running down the rows
        uint64_t outer = 1;
        for (size_t i = 0; i < axis; i++) {
            outer *= x.dimensions()[i];
        }
        uint64_t const length = x.dimensions()[axis];
        uint64_t inner = 1;
        for (size_t i = axis + 1u; i < x.rank(); i++) {
            inner *= x.dimensions()[i];
        }

        BOOST_OUTCOME_TRY(
            auto const out, interpreter_.allocate_tensor(x.dtype(), x.shape()));
        visit_dtype(x.dtype(), [&]<typename T>() {
            auto const xs = x.elements<T const>();
            auto const outs = out.elements<T>();
            for (uint64_t block = 0; block < outer; block++) {
                for (uint64_t row = 0; row < length; row++) {
                    uint64_t const start = (block * length + row) * inner;
                    for (uint64_t i = start; i < start + inner; i++) {
                        outs[i] = row == 0
                                      ? xs[i]
                                      : WrappingAdd{}(outs[i - inner], xs[i]);
                    }
                }
            }
        });
        return out;
    }
};

Result<Tensor> op_TensorRef(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_MatMul(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_ArgMax(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_ArgMin(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_Clip(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_Max(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_Min(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_Mul(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_Div(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<Tensor> op_Cast(State &, std::span<uint8_t const>)
{
    return GraphEvalError::InternalError;
}

Result<std::vector<Tensor>> Interpreter::run()
{
    // The previous evaluation on this thread is over: its caller encodes the
    // outputs as soon as run() returns, with nothing in between that could
    // suspend the fiber and let another evaluation start. That would no longer
    // hold if an op could suspend, for instance to read state.
    thread_arena().reset();

    BOOST_OUTCOME_TRY(check_magic_number());
    BOOST_OUTCOME_TRY(check_inputs());

    // Read output-tensor indices. TODO: constrain number of outputs
    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(graphcode_));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    std::array<uint16_t, MAX_GRAPH_OUTPUTS> outputs{};
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(outputs[i], read_next<uint16_t>(graphcode_));
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(graphcode_));
    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(
            auto const opcode_id, read_next<uint16_t>(graphcode_));
        if (opcode_id > static_cast<uint16_t>(Op::Last_valid_op)) {
            return GraphEvalError::GraphValidationError;
        }
        auto const opcode = static_cast<Op>(opcode_id);

        auto const start = std::chrono::steady_clock::now();
        Tensor result;
        switch (opcode) {
        case Op::Literal: {
            BOOST_OUTCOME_TRY(
                result, LiteralOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::TensorRef: {
            BOOST_OUTCOME_TRY(result, op_TensorRef(state_, graphcode_));
            break;
        }
        case Op::Add: {
            BOOST_OUTCOME_TRY(result, AddOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Sub: {
            BOOST_OUTCOME_TRY(result, SubOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Greater: {
            BOOST_OUTCOME_TRY(
                result, GreaterOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Ge: {
            BOOST_OUTCOME_TRY(result, GeOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Equal: {
            BOOST_OUTCOME_TRY(result, EqualOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Reshape: {
            BOOST_OUTCOME_TRY(
                result, ReshapeOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Where: {
            BOOST_OUTCOME_TRY(result, WhereOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::CumSum: {
            BOOST_OUTCOME_TRY(
                result, CumSumOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::Saturate: {
            BOOST_OUTCOME_TRY(
                result, SaturateOp{*this}(graphcode_, node_values_));
            break;
        }
        case Op::MatMul: {
            BOOST_OUTCOME_TRY(result, op_MatMul(state_, graphcode_));
            break;
        }
        case Op::ArgMax: {
            BOOST_OUTCOME_TRY(result, op_ArgMax(state_, graphcode_));
            break;
        }
        case Op::ArgMin: {
            BOOST_OUTCOME_TRY(result, op_ArgMin(state_, graphcode_));
            break;
        }
        case Op::Clip: {
            BOOST_OUTCOME_TRY(result, op_Clip(state_, graphcode_));
            break;
        }
        case Op::Max: {
            BOOST_OUTCOME_TRY(result, op_Max(state_, graphcode_));
            break;
        }
        case Op::Min: {
            BOOST_OUTCOME_TRY(result, op_Min(state_, graphcode_));
            break;
        }
        case Op::Mul: {
            BOOST_OUTCOME_TRY(result, op_Mul(state_, graphcode_));
            break;
        }
        case Op::Div: {
            BOOST_OUTCOME_TRY(result, op_Div(state_, graphcode_));
            break;
        }
        case Op::Cast: {
            BOOST_OUTCOME_TRY(result, op_Cast(state_, graphcode_));
            break;
        }
        case Op::Expand: {
            BOOST_OUTCOME_TRY(
                result, ExpandOp{*this}(graphcode_, node_values_));
            break;
        }
        }
        auto const end = std::chrono::steady_clock::now();
        node_values_.push_back(result);
        if constexpr (PRINT_NODE_TIMES) {
            print_node_time(
                node_values_.size() - 1, opcode, result, end - start);
        }
    }

    // Output indices are read before the ops, so they can only be checked once
    // every node exists
    std::vector<Tensor> output_values;
    output_values.reserve(n_outputs);
    for (size_t i = 0; i < n_outputs; i++) {
        if (outputs[i] >= node_values_.size()) {
            return GraphEvalError::GraphValidationError;
        }
        output_values.push_back(node_values_[outputs[i]]);
    }
    return output_values;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
