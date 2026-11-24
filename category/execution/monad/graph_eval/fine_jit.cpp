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

#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/fine.hpp"
#include "category/execution/monad/graph_eval/fixed_point.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/matmul.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include "category/execution/monad/graph_eval/unaligned.hpp"
#include <bit>
#include <category/execution/monad/graph_eval/fine_jit.hpp>
#include <limits>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

constexpr size_t VECTOR_WIDTH = 64;

struct AxisSplit
{
    uint64_t outer;
    uint64_t length;
    uint64_t inner;
};

[[gnu::always_inline]]
inline AxisSplit split_at(Shape const &shape, size_t const axis)
{
    AxisSplit split{1, shape.dimensions()[axis], 1};
    for (size_t d = 0; d < axis; d++) {
        split.outer *= shape.dimensions()[d];
    }
    for (size_t d = axis + 1; d < shape.rank(); d++) {
        split.inner *= shape.dimensions()[d];
    }
    return split;
}

void concat(Tensor const &x, Tensor const &y, size_t const axis, Tensor &out)
{
    size_t const size = dtype_size(x.type().dtype());
    AxisSplit const xs = split_at(x.type().shape(), axis);
    AxisSplit const ys = split_at(y.type().shape(), axis);
    uint64_t const x_row = xs.length * xs.inner * size;
    uint64_t const y_row = ys.length * ys.inner * size;
    for (uint64_t o = 0; o < xs.outer; o++) {
        uint8_t *const row = out.data() + o * (x_row + y_row);
        std::memcpy(row, x.data() + o * x_row, x_row);
        std::memcpy(row + x_row, y.data() + o * y_row, y_row);
    }
}

bool gather(
    Tensor const &x, Tensor const &indices, size_t const axis, Tensor &out)
{
    size_t const size = dtype_size(x.type().dtype());
    AxisSplit const xs = split_at(x.type().shape(), axis);
    uint64_t const slice = xs.inner * size;
    uint64_t const count = indices.type().shape().size();
    return visit_dtype(indices.type().dtype(), [&]<typename I>() -> bool {
        auto const *const index = as_elements<I>(indices.data());
        for (uint64_t k = 0; k < count; k++) {
            if (std::cmp_less(I{index[k]}, 0) ||
                std::cmp_greater_equal(I{index[k]}, xs.length)) {
                return false;
            }
        }
        for (uint64_t o = 0; o < xs.outer; o++) {
            for (uint64_t k = 0; k < count; k++) {
                // Checked to be in [0, length) above
                auto const i = static_cast<uint64_t>(
                    static_cast<std::make_unsigned_t<I>>(I{index[k]}));
                std::memcpy(
                    out.data() + (o * count + k) * slice,
                    x.data() + (o * xs.length + i) * slice,
                    slice);
            }
        }
        return true;
    });
}

template <typename T>
[[gnu::always_inline]]
inline T wrapping_add(T const x, T const y)
{
    T result;
    (void)__builtin_add_overflow(x, y, &result);
    return result;
}

template <typename T>
[[gnu::always_inline]]
inline T wrapping_sub(T const x, T const y)
{
    T result;
    (void)__builtin_sub_overflow(x, y, &result);
    return result;
}

template <typename T>
[[gnu::always_inline]]
inline T wrapping_mul(T const x, T const y)
{
    T result;
    (void)__builtin_mul_overflow(x, y, &result);
    return result;
}

template <typename T>
[[gnu::always_inline]]
inline T divc_pow2(T const x, size_t const exp)
{
    if constexpr (std::is_signed_v<T>) {
        auto const bias =
            static_cast<T>((std::make_unsigned_t<T>{1} << exp) - 1);
        return static_cast<T>((x < 0 ? x + bias : x) >> exp);
    }
    else {
        return static_cast<T>(x >> exp);
    }
}

template <typename T>
[[gnu::always_inline]]
inline T divc(T const x, uint64_t const y)
{
    if constexpr (std::is_signed_v<T>) {
        uint64_t const magnitude = x < 0
                                       ? uint64_t{0} - static_cast<uint64_t>(x)
                                       : static_cast<uint64_t>(x);
        uint64_t const quotient = magnitude / y;
        return static_cast<T>(x < 0 ? uint64_t{0} - quotient : quotient);
    }
    else {
        return static_cast<T>(static_cast<uint64_t>(x) / y);
    }
}

template <typename In, typename Out>
[[gnu::always_inline]]
inline Out saturate(In const x)
{
    using InLimits = std::numeric_limits<In>;
    using OutLimits = std::numeric_limits<Out>;
    constexpr In lo = std::cmp_less(OutLimits::min(), InLimits::min())
                          ? InLimits::min()
                          : static_cast<In>(OutLimits::min());
    constexpr In hi = std::cmp_greater(OutLimits::max(), InLimits::max())
                          ? InLimits::max()
                          : static_cast<In>(OutLimits::max());
    return static_cast<Out>(std::clamp(x, lo, hi));
}

template <typename T>
[[gnu::always_inline]]
inline uint8_t less_than(T const x, T const y)
{
    return x < y;
}

template <typename T>
[[gnu::always_inline]]
inline uint8_t less_equal(T const x, T const y)
{
    return x <= y;
}

template <typename T>
[[gnu::always_inline]]
inline T min(T const x, T const y)
{
    return std::min(x, y);
}

template <typename T>
[[gnu::always_inline]]
inline T max(T const x, T const y)
{
    return std::max(x, y);
}

template <typename T, auto F>
[[gnu::always_inline]] inline void combine_row(
    T const *__restrict const prev, unaligned_t<T> const *__restrict const x,
    T *__restrict const out, uint64_t const n)
{
    for (uint64_t i = 0; i < n; i++) {
        out[i] = F(prev[i], T{x[i]});
    }
}

void cumsum(Tensor const &x, size_t const axis, Tensor &out)
{
    AxisSplit const s = split_at(x.type().shape(), axis);
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        auto const *const xs = as_elements<T>(x.data());
        T *const outs = reinterpret_cast<T *>(out.data());
        for (uint64_t o = 0; o < s.outer; o++) {
            for (uint64_t r = 0; r < s.length; r++) {
                uint64_t const at = (o * s.length + r) * s.inner;
                if (r == 0) {
                    std::memcpy(outs + at, xs + at, s.inner * sizeof(T));
                }
                else {
                    combine_row<T, wrapping_add<T>>(
                        outs + at - s.inner, xs + at, outs + at, s.inner);
                }
            }
        }
    });
}

template <typename T, auto F>
[[gnu::always_inline]] inline void accumulate_row(
    T *__restrict const acc, unaligned_t<T> const *__restrict const x,
    uint64_t const n)
{
    for (uint64_t i = 0; i < n; i++) {
        acc[i] = F(acc[i], T{x[i]});
    }
}

template <typename T, auto F>
T reduce_contiguous(unaligned_t<T> const *__restrict const x, uint64_t const n)
{
    constexpr size_t L = VECTOR_WIDTH / sizeof(T);
    uint64_t i = 0;
    T result = x[0];
    if (sizeof(T) == 8 && n >= 2 * L) {
        T lanes[L];
        for (size_t j = 0; j < L; j++) {
            lanes[j] = x[j];
        }
        for (i = L; i + L <= n; i += L) {
            for (size_t j = 0; j < L; j++) {
                lanes[j] = F(lanes[j], T{x[i + j]});
            }
        }
        result = lanes[0];
        for (size_t j = 1; j < L; j++) {
            result = F(result, lanes[j]);
        }
    }
    else {
        i = 1;
    }
    for (; i < n; i++) {
        result = F(result, T{x[i]});
    }
    return result;
}

void reduce_sum(Tensor const &x, size_t const axis, Tensor &out)
{
    AxisSplit const s = split_at(x.type().shape(), axis);
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        constexpr auto const sum = [](T const x, T const y) -> T {
            return wrapping_add(x, y);
        };
        auto const *const xs = as_elements<T>(x.data());
        T *const outs = reinterpret_cast<T *>(out.data());
        for (uint64_t o = 0; o < s.outer; o++) {
            auto const *const rows = xs + o * s.length * s.inner;
            T *const result = outs + o * s.inner;
            if (s.inner == 1) {
                *result = reduce_contiguous<T, sum>(rows, s.length);
                continue;
            }
            std::memcpy(result, rows, s.inner * sizeof(T));
            for (uint64_t r = 1; r < s.length; r++) {
                accumulate_row<T, sum>(result, rows + r * s.inner, s.inner);
            }
        }
    });
}

void reduce_max(Tensor const &x, size_t const axis, Tensor &out)
{
    AxisSplit const s = split_at(x.type().shape(), axis);
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        constexpr auto const max = [](T const x, T const y) {
            return std::max(x, y);
        };
        auto const *const xs = as_elements<T>(x.data());
        T *const outs = reinterpret_cast<T *>(out.data());
        for (uint64_t o = 0; o < s.outer; o++) {
            auto const *const rows = xs + o * s.length * s.inner;
            T *const result = outs + o * s.inner;
            if (s.inner == 1) {
                *result = reduce_contiguous<T, max>(rows, s.length);
                continue;
            }
            std::memcpy(result, rows, s.inner * sizeof(T));
            for (uint64_t r = 1; r < s.length; r++) {
                accumulate_row<T, max>(result, rows + r * s.inner, s.inner);
            }
        }
    });
}

void arg_min(Tensor const &x, Tensor &out)
{
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        auto const *const xs = as_elements<T>(x.data());
        uint64_t const n = x.type().shape().size();
        uint64_t best = 0;
        for (uint64_t i = 1; i < n; i++) {
            if (xs[i] < xs[best]) {
                best = i;
            }
        }
        *reinterpret_cast<T *>(out.data()) = static_cast<T>(best);
    });
}

void arg_max(Tensor const &x, Tensor &out)
{
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        auto const *const xs = as_elements<T>(x.data());
        uint64_t const n = x.type().shape().size();
        uint64_t best = 0;
        for (uint64_t i = 1; i < n; i++) {
            if (xs[i] > xs[best]) {
                best = i;
            }
        }
        *reinterpret_cast<T *>(out.data()) = static_cast<T>(best);
    });
}

static constexpr size_t SCALAR_BLOCK_SIZE = 256;

#define FAT_FN_LIST                                                            \
    NO_DISPATCH(Stop), WIDTH_DISPATCH(Add), WIDTH_DISPATCH(Sub),               \
        FULL_DISPATCH(Mul), FULL_DISPATCH(Divc), FULL_DISPATCH(Div),           \
        FULL_DISPATCH(Lt), FULL_DISPATCH(Le), WIDTH_DISPATCH(Eq),              \
        WIDTH_DISPATCH(Where), FULL_DISPATCH(Min), FULL_DISPATCH(Max),         \
        SATURATE_DISPATCH(Saturate), FULL_DISPATCH(QMul), FULL_DISPATCH(QDiv), \
        FULL_DISPATCH(QExp), WIDTH_DISPATCH(QInvSqrt), WIDTH_DISPATCH(ISqrt),

#define NO_DISPATCH(Name) Name
#define WIDTH_DISPATCH(Name) Name##8, Name##16, Name##32, Name##64
#define FULL_DISPATCH(Name) WIDTH_DISPATCH(Name##u), WIDTH_DISPATCH(Name##i)
#define SATURATE_DISPATCH(Name)                                                \
    FULL_DISPATCH(Name##u8), FULL_DISPATCH(Name##u16),                         \
        FULL_DISPATCH(Name##u32), FULL_DISPATCH(Name##u64),                    \
        FULL_DISPATCH(Name##i8), FULL_DISPATCH(Name##i16),                     \
        FULL_DISPATCH(Name##i32), FULL_DISPATCH(Name##i64)

enum class FatFn : uint16_t
{
    FAT_FN_LIST

        Invalid,
};
#undef SATURATE_DISPATCH
#undef FULL_DISPATCH
#undef WIDTH_DISPATCH
#undef NO_DISPATCH

struct ScalarRegisterFile
{
    std::array<uint8_t *, MAX_SCALAR_REGISTERS + 1> registers;
    std::array<Dtype, MAX_SCALAR_REGISTERS + 1> types;
};

using FnEval =
    bool (*)(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);

#if defined(__has_attribute)
    #if __has_attribute(musttail)
        #define MONAD_GRAPH_MUST_TAIL __attribute__((musttail))
    #else
        #error "No compiler support for __attribute__((musttail))"
    #endif
#else
    #error "No compiler support for __has_attribute"
#endif

// The fn has read its operands, so instr_ptr is at the next fn's opcode (one
// byte). The next fn gets a pointer to the byte after it, its first operand
#define MONAD_GRAPH_SCALAR_NEXT                                                \
    do {                                                                       \
        MONAD_GRAPH_MUST_TAIL return fn_table<traits>[*instr_ptr](             \
            n, registers, instr_ptr + 1);                                      \
    }                                                                          \
    while (false);

template <Traits traits>
bool StopEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool AddEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool SubEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool MulEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool DivcEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool DivEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool LtEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool LeEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool EqEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool WhereEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool MinEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool MaxEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
    requires std::is_unsigned_v<dtype>
bool ISqrtEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool QMulEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool QDivEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool QExpEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype>
bool QInvSqrtEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);
template <Traits traits, dtype_t dtype1, dtype_t dtype2>
bool SaturateEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr);

#define NO_DISPATCH(Name) Name##Eval<traits>
#define SINGLE_DISPATCH(Name, sgn)                                             \
    Name##Eval<traits, sgn##int8_t>, Name##Eval<traits, sgn##int16_t>,         \
        Name##Eval<traits, sgn##int32_t>, Name##Eval<traits, sgn##int64_t>
#define WIDTH_DISPATCH(Name) SINGLE_DISPATCH(Name, u)
#define FULL_DISPATCH(Name) SINGLE_DISPATCH(Name, u), SINGLE_DISPATCH(Name, )
// One In type to every Out type, in the enum's order: u8 ... u64, i8 ... i64
#define SATURATE_ROW(Name, In)                                                 \
    Name##Eval<traits, In, uint8_t>, Name##Eval<traits, In, uint16_t>,         \
        Name##Eval<traits, In, uint32_t>, Name##Eval<traits, In, uint64_t>,    \
        Name##Eval<traits, In, int8_t>, Name##Eval<traits, In, int16_t>,       \
        Name##Eval<traits, In, int32_t>, Name##Eval<traits, In, int64_t>
#define SATURATE_DISPATCH(Name)                                                \
    SATURATE_ROW(Name, uint8_t), SATURATE_ROW(Name, uint16_t),                 \
        SATURATE_ROW(Name, uint32_t), SATURATE_ROW(Name, uint64_t),            \
        SATURATE_ROW(Name, int8_t), SATURATE_ROW(Name, int16_t),               \
        SATURATE_ROW(Name, int32_t), SATURATE_ROW(Name, int64_t)

template <Traits traits>
consteval std::array<FnEval, static_cast<size_t>(FatFn::Invalid)>
make_fn_table()
{
    return {FAT_FN_LIST};
}

template <Traits traits>
constexpr std::array<FnEval, static_cast<size_t>(FatFn::Invalid)> fn_table =
    make_fn_table<traits>();
#undef SATURATE_DISPATCH
#undef SATURATE_ROW
#undef FULL_DISPATCH
#undef WIDTH_DISPATCH
#undef SINGLE_DISPATCH
#undef NO_DISPATCH

#define FN_PARAM(T, name) T const name = take<T>(instr_ptr)
#define FN_INPUT(T, name)                                                      \
    unaligned_t<T> const *__restrict const name =                              \
        reinterpret_cast<unaligned_t<T> const *>(                              \
            registers.registers[take<register_id_t>(instr_ptr)])
#define FN_OUTPUT(T, name)                                                     \
    unaligned_t<T> *__restrict const name =                                    \
        reinterpret_cast<unaligned_t<T> *>(                                    \
            registers.registers[take<register_id_t>(instr_ptr)])

template <typename... Ts>
constexpr size_t block_elements = std::max(
    VECTOR_WIDTH / std::max({sizeof(Ts)...}), 16 / std::min({sizeof(Ts)...}));

template <auto F, Unaligned X, Unaligned Out, typename... Ts>
[[gnu::always_inline]] inline void map1(
    size_t const n, X const *__restrict const x, Out *__restrict const out,
    Ts... args)
{
    static_assert(std::is_same_v<
                  unaligned_t<decltype(F(std::declval<X>(), args...))>,
                  Out>);
    constexpr size_t B = block_elements<Out, X>;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            out[i + j] = F(X{x[i + j]}, args...);
        }
    }
    for (; i < n; i++) {
        out[i] = F(X{x[i]}, args...);
    }
}

template <auto F, Unaligned X, Unaligned Y, Unaligned Out, typename... Ts>
[[gnu::always_inline]] inline void map2(
    size_t const n, X const *__restrict const x, Y const *__restrict const y,
    Out *__restrict const out, Ts... args)
{
    static_assert(std::is_same_v<
                  unaligned_t<decltype(F(
                      std::declval<X>(), std::declval<Y>(), args...))>,
                  Out>);
    constexpr size_t B = block_elements<Out, X, Y>;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            out[i + j] = F(X{x[i + j]}, Y{y[i + j]}, args...);
        }
    }
    for (; i < n; i++) {
        out[i] = F(X{x[i]}, Y{y[i]}, args...);
    }
}

template <
    auto F, Unaligned X, Unaligned Y, Unaligned Z, Unaligned Out,
    typename... Ts>
[[gnu::always_inline]] inline void map3(
    size_t const n, X const *__restrict const x, Y const *__restrict const y,
    Z const *__restrict const z, Out *__restrict const out, Ts... args)
{
    static_assert(std::is_same_v<
                  unaligned_t<decltype(F(
                      std::declval<X>(),
                      std::declval<Y>(),
                      std::declval<Z>(),
                      args...))>,
                  Out>);
    constexpr size_t B = block_elements<Out, X, Y>;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            out[i + j] = F(X{x[i + j]}, Y{y[i + j]}, Z{z[i + j]}, args...);
        }
    }
    for (; i < n; i++) {
        out[i] = F(X{x[i]}, Y{y[i]}, Z{z[i]}, args...);
    }
}

template <Traits traits>
bool StopEval(size_t const, ScalarRegisterFile &, uint8_t const *)
{
    return true;
}

template <Traits traits, dtype_t T>
bool AddEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    map2<wrapping_add<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool SubEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    map2<wrapping_sub<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool MulEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    map2<wrapping_mul<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool DivcEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_PARAM(uint64_t, divisor);
    FN_INPUT(T, x);
    FN_OUTPUT(T, out);

    if (std::has_single_bit(divisor)) {
        auto const shift = static_cast<uint8_t>(std::countr_zero(divisor));
        if (shift >= 8 * sizeof(T)) {
            // |x| < 2^shift, so every quotient is 0
            std::memset(out, 0, n * sizeof(T));
        }
        else {
            map1<divc_pow2<T>>(n, x, out, shift);
        }
    }
    else {
        map1<divc<T>>(n, x, out, divisor);
    }

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Unaligned T>
[[gnu::always_inline]]
inline bool contains_zero(size_t const n, T const *__restrict const x)
{
    bool zero = false;
    for (size_t i = 0; i < n; i++) {
        zero |= T{x[i]} == 0;
    }
    return zero;
}

template <Traits traits, dtype_t T>
bool DivEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    if (contains_zero(n, y)) {
        return false;
    }

    // TODO specialize this
    map2<[](T const x, T const y) { return q_div(x, y, 0); }>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool LtEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(uint8_t, out);

    map2<less_than<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool LeEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(uint8_t, out);

    map2<less_equal<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool EqEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(uint8_t, out);

    map2<[](T const x, T const y) -> uint8_t { return x == y; }>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool WhereEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(uint8_t, cond);
    FN_INPUT(T, branch_t);
    FN_INPUT(T, branch_f);
    FN_OUTPUT(T, out);

    map3<
        [](uint8_t const cond, T const x, T const y) -> T {
            return cond ? x : y;
        },
        unaligned_t<uint8_t>,
        unaligned_t<T>,
        unaligned_t<T>>(n, cond, branch_t, branch_f, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool MinEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    map2<min<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool MaxEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    map2<max<T>>(n, x, y, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
    requires std::is_unsigned_v<T>
bool ISqrtEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(T, x);
    FN_OUTPUT(T, out);

    map1<floor_sqrt<T>>(n, x, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool QMulEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_PARAM(uint8_t, frac_bits);
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    map2<q_mul<T>>(n, x, y, out, frac_bits);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool QDivEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_PARAM(uint8_t, frac_bits);
    FN_INPUT(T, x);
    FN_INPUT(T, y);
    FN_OUTPUT(T, out);

    if (contains_zero(n, y)) {
        return false;
    }

    map2<q_div<T>>(n, x, y, out, frac_bits);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool QExpEval(size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_PARAM(uint8_t, frac_bits);
    FN_INPUT(T, x);
    FN_OUTPUT(T, out);

    map1<q_exp<T>>(n, x, out, frac_bits);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t T>
bool QInvSqrtEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_PARAM(uint8_t, frac_bits);
    FN_INPUT(T, x);
    FN_OUTPUT(T, out);

    if (contains_zero(n, x)) {
        return false;
    }
    map1<q_inv_sqrt<T>>(n, x, out, frac_bits);

    MONAD_GRAPH_SCALAR_NEXT;
}

template <Traits traits, dtype_t In, dtype_t Out>
bool SaturateEval(
    size_t n, ScalarRegisterFile &registers, uint8_t const *instr_ptr)
{
    FN_INPUT(In, x);
    FN_OUTPUT(Out, out);

    map1<saturate<In, Out>>(n, x, out);

    MONAD_GRAPH_SCALAR_NEXT;
}

#undef FN_OUTPUT
#undef FN_INPUT

#undef MONAD_GRAPH_SCALAR_NEXT
#undef MONAD_GRAPH_MUST_TAIL

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

[[gnu::always_inline]]
inline Tensor FineJit::node(size_t const id) const
{
    // TODO: this is bad
    uint32_t const location = finecode_.node_location(id);
    uint8_t const *const data =
        (location & FINE_CODE_LOCATION)
            ? finecode_.ops() + (location & ~FINE_CODE_LOCATION)
            : arena_ + location;
    return Tensor{finecode_.node_type(id), const_cast<uint8_t *>(data)};
}

// Copy the inputs into the arena.
Result<void> FineJit::load_inputs()
{
    if (inputs_.size() != finecode_.n_inputs()) {
        return GraphEvalError::ArityError;
    }
    for (size_t i = 0; i < inputs_.size(); i++) {
        TensorType const &expected = finecode_.node_type(i);
        if (inputs_[i].type.dtype() != expected.dtype()) {
            return GraphEvalError::TypeError;
        }
        if (inputs_[i].type.shape() != expected.shape()) {
            return GraphEvalError::ShapeError;
        }
    }
    for (size_t i = 0; i < inputs_.size(); i++) {
        TensorInput const &input = inputs_[i];
        Tensor tensor = node(i);
        if (auto const *const data =
                std::get_if<byte_string_view>(&input.source)) {
            copy_elements(
                input.type.dtype(), input.byte_order, *data, tensor.data());
        }
        else if (auto const *const ref = std::get_if<CodeRef>(&input.source)) {
            BOOST_OUTCOME_TRY(
                load_code_tensor(state_, *ref, input.byte_order, tensor));
        }
        else {
            // TODO: implement storage references.
            MONAD_ABORT();
        }
    }
    return outcome::success();
}

[[gnu::always_inline]]
// TODO: this doesn't need to return a value
Tensor FineJit::take_input()
{
    return node(take<node_id_t>(code_));
}

enum class ScalarInputKind
{
    Exact,
    Broadcast,
    Replicate
};

struct ScalarInput
{
    uint8_t const *data;
    size_t elt_size;
    ScalarInputKind kind;
    size_t rank;
    std::array<uint64_t, MAX_RANK> dims;
    std::array<uint64_t, MAX_RANK> strides;
    std::array<uint64_t, MAX_RANK> index;
    uint64_t row;
};

template <typename T>
void fill_register(size_t n, uint8_t const *input, uint8_t *reg)
{
    std::fill_n(reg, n, *reinterpret_cast<unaligned_t<T> const *>(input));
}

Result<void> FineJit::run_scalar(Tensor const out)
{
    auto const &shape = out.type().shape();
    auto const size = shape.size();
    auto const elt_size = dtype_size(out.type().dtype());

    ScalarRegisterFile register_file;
    register_file.types[MAX_SCALAR_REGISTERS] = out.type().dtype();

    skip<Shape>(code_);
    auto const n_inputs = take<uint8_t>(code_);
    std::array<ScalarInput, MAX_SCALAR_INPUTS> inputs;
    for (size_t i = 0; i < n_inputs; i++) {
        auto const input_tensor = take_input();
        auto const &input_type = input_tensor.type();
        inputs[i].data = input_tensor.data();
        inputs[i].elt_size = dtype_size(input_type.dtype());
        register_file.types[i] = input_type.dtype();
        if (input_type.shape().size() == size) {
            inputs[i].kind = ScalarInputKind::Exact;
        }
        else if (input_type.shape().size() == 1) {
            // Scalar inputs are copied to a register once.
            inputs[i].kind = ScalarInputKind::Replicate;
            auto const length =
                std::min(size, SCALAR_BLOCK_SIZE * sizeof(uint64_t));
            uint8_t const *const input_data = inputs[i].data;
            uint8_t *const reg_data = register_file.registers[i];
            switch (inputs[i].elt_size) {
            case 1:
                fill_register<uint8_t>(length, input_data, reg_data);
                break;
            case 2:
                fill_register<uint16_t>(length, input_data, reg_data);
                break;
            case 4:
                fill_register<uint32_t>(length, input_data, reg_data);
                break;
            case 8:
                fill_register<uint64_t>(length, input_data, reg_data);
                break;
            default:
                MONAD_ABORT();
            }
        }
        else {
            inputs[i].kind = ScalarInputKind::Broadcast;
        }
    }
}

Result<GraphOutputs> FineJit::run()
{
    if (finecode_.validation_result() != GraphEvalError::Success) {
        return finecode_.validation_result();
    }
    if (output_count_.has_value() &&
        *output_count_ != finecode_.output_ids().size()) {
        return GraphEvalError::ArityError;
    }

    BOOST_OUTCOME_TRY(load_inputs());

    for (size_t i = 0; i < finecode_.n_ops(); i++) {
        auto const id = i + finecode_.n_inputs();
        auto out = node(id);
        auto const op = take<FineOp>(code_);
        switch (op) {
        case FineOp::Scalar: {
            run_scalar(out);
            break;
        }
        case FineOp::Literal: {
            // Literals are referenced in-place, no need to copy.
            skip<TensorType>(code_);
            skip_bytes(code_, finecode_.node_type(id).size_bytes());
            break;
        }
        case FineOp::TensorRef: {
            skip<TensorType>(code_);
            auto const address = take<Address>(code_);
            auto const offset = take<uint32_t>(code_);
            BOOST_OUTCOME_TRY(load_code_tensor(
                state_,
                CodeRef{address, offset},
                ByteOrder::LittleEndian,
                out));
            break;
        }
        case FineOp::Reshape:
            // Reshapes have no effect other than affecting the list of node
            // types.
            skip<Shape>(code_);
            skip<node_id_t>(code_);
            break;
        case FineOp::Concat: {
            auto const axis = take<uint8_t>(code_);
            auto const x = take_input();
            auto const y = take_input();
            concat(x, y, axis, out);
            break;
        }
        case FineOp::MatMul: {
            auto const x = take_input();
            auto const y = take_input();
            matmul_i8(x, y, out);
            break;
        }
        case FineOp::QMatMul: {
            auto const bits = take<uint8_t>(code_);
            skip<Dtype>(code_);
            auto const x = take_input();
            auto const y = take_input();
            qmatmul(x, y, bits, out);
            break;
        }
        case FineOp::CumSum: {
            auto const axis = take<uint8_t>(code_);
            auto const x = take_input();
            cumsum(x, axis, out);
            break;
        }
        case FineOp::ArgMin: {
            auto const x = take_input();
            arg_min(x, out);
            break;
        }
        case FineOp::ArgMax: {
            auto const x = take_input();
            arg_max(x, out);
            break;
        }
        case FineOp::ReduceSum: {
            auto const axis = take<uint8_t>(code_);
            auto const x = take_input();
            reduce_sum(x, axis, out);
            break;
        }
        case FineOp::ReduceMax: {
            auto const axis = take<uint8_t>(code_);
            auto const x = take_input();
            reduce_max(x, axis, out);
            break;
        }
        case FineOp::Gather: {
            auto const axis = take<uint8_t>(code_);
            auto const x = take_input();
            auto const indices = take_input();
            if (!gather(x, indices, axis, out)) {
                return GraphEvalError::IndexError;
            };
            break;
        }
        case FineOp::Invalid:
            // Impossible, since the code has passed validation
            MONAD_ABORT();
        }
    }

    auto const &output_ids = finecode_.output_ids();
    GraphOutputs outputs;
    outputs.count = output_ids.size();
    for (size_t i = 0; i < output_ids.size(); i++) {
        outputs.tensors[i] = node(output_ids[i]);
    }
    return outputs;
}

MONAD_GRAPH_EVAL_NAMESPACE_END

// Instantiates the fn table, and with it every fn template, so that
// std::max<T>rrors in the templates show up when this file is compiled
MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN
template std::array<FnEval, static_cast<size_t>(FatFn::Invalid)> const
    fn_table<MonadTraits<MONAD_NEXT>>;
MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END
