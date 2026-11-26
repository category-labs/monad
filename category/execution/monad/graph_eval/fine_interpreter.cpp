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

#include "category/execution/monad/graph_eval/unaligned.hpp"
#include <category/core/assert.h>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/fine.hpp>
#include <category/execution/monad/graph_eval/fine_interpreter.hpp>
#include <category/execution/monad/graph_eval/fixed_point.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/matmul.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <span>
#include <type_traits>
#include <utility>
#include <variant>

#if defined(__AVX512BW__)
    #include <immintrin.h>
#endif

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// The elements of a chunk: each register's block holds a chunk of the widest
// dtype
constexpr size_t SCALAR_CHUNK = 256;

// A zmm register's bytes, which a kernel's block of elements fills
constexpr size_t SCALAR_VECTOR = 64;

// A register: where the current chunk's elements are, and their dtype. A
// uniform register has the same value at every position: it was computed
// once and copied across the chunk, so that a fn whose operands are all
// uniform runs once a chunk rather than once an element
struct ScalarRegister
{
    uint8_t const *data;
    bool uniform;
    Dtype dtype;
};

struct ScalarRegisters
{
    // 14 x 2 KiB: an input's expanded chunk or copies of its one element, a
    // constant's copies, or a fn's result, for the register of the same number
    alignas(SCALAR_VECTOR)
        uint8_t blocks[MAX_SCALAR_REGISTERS][SCALAR_CHUNK * sizeof(uint64_t)];
    std::array<ScalarRegister, MAX_SCALAR_REGISTERS> registers;
};

MONAD_GRAPH_EVAL_NAMESPACE_END

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

//
// Reading validated bytecode, so without bounds checks
//

// A fn's params, or none for std::monostate
template <FineFn Fn>
[[gnu::always_inline]] inline FnParams<Fn>
take_params(uint8_t const *&code)
{
    if constexpr (std::is_same_v<FnParams<Fn>, std::monostate>) {
        return {};
    }
    else {
        return take<FnParams<Fn>>(code);
    }
}

//
// Elements at any address
//

// T with alignment 1, to read and write elements at any address, as a
// Literal's are in the code. It has to be formed here, from T: an aligned(1)
// typedef given as a template argument loses its attribute (FINDINGS.md)
//
// Scalar kernels: out[i] = f(x[i], ...) for i < n, every operand a full
// chunk. They run in blocks of B elements, whose inner loop has a fixed
// count, which GCC vectorizes at -O2 even for short chunks: a plain loop over
// n gets vectors as long as its narrowest dtype's, 64 elements for an 8-bit
// one, and runs any shorter chunk scalar. B fills a zmm register with the
// widest dtype, or 16 bytes with the narrowest if that's more: GCC leaves a
// block of 8 bytes, as of int64 compared into uint8, scalar. The last,
// partial block has exactly the elements left: padding could fail, as a
// division by zero does. Each is its own function, with __restrict pointers,
// so that GCC can vectorize it without checking for overlap; registers don't
// overlap, though the validator doesn't check that a fn's destination isn't
// one of its operands
//

template <typename... Ts>
constexpr size_t block_elements = std::max(
    SCALAR_VECTOR / std::max({sizeof(Ts)...}), 16 / std::min({sizeof(Ts)...}));

template <typename Out, typename X, typename F>
[[gnu::noinline]] void map1(
    unaligned_t<X> const *__restrict const x,
    unaligned_t<Out> *__restrict const out, size_t const n, F const f)
{
    constexpr size_t B = block_elements<Out, X>;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            out[i + j] = f(X{x[i + j]});
        }
    }
    for (; i < n; i++) {
        out[i] = f(X{x[i]});
    }
}

template <typename Out, typename X, typename Y, typename F>
[[gnu::noinline]] void map2(
    unaligned_t<X> const *__restrict const x,
    unaligned_t<Y> const *__restrict const y,
    unaligned_t<Out> *__restrict const out, size_t const n, F const f)
{
    constexpr size_t B = block_elements<Out, X, Y>;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            out[i + j] = f(X{x[i + j]}, Y{y[i + j]});
        }
    }
    for (; i < n; i++) {
        out[i] = f(X{x[i]}, Y{y[i]});
    }
}

template <typename Out, typename C, typename X, typename Y, typename F>
[[gnu::noinline]] void map3(
    unaligned_t<C> const *__restrict const c,
    unaligned_t<X> const *__restrict const x,
    unaligned_t<Y> const *__restrict const y,
    unaligned_t<Out> *__restrict const out, size_t const n, F const f)
{
    constexpr size_t B = block_elements<Out, C, X, Y>;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            out[i + j] = f(C{c[i + j]}, X{x[i + j]}, Y{y[i + j]});
        }
    }
    for (; i < n; i++) {
        out[i] = f(C{c[i]}, X{x[i]}, Y{y[i]});
    }
}

// Whether p(x[i]) for any i < n, in the same blocks: the check before a fn
// that can fail. The OR is of integers, which GCC vectorizes, as it doesn't a
// bool's
template <typename X, typename P>
[[gnu::noinline]] bool
any_of(unaligned_t<X> const *__restrict const x, size_t const n, P const p)
{
    constexpr size_t B = block_elements<X>;
    std::make_unsigned_t<X> found = 0;
    size_t i = 0;
    for (; i + B <= n; i += B) {
        for (size_t j = 0; j < B; j++) {
            found |= p(X{x[i + j]});
        }
    }
    for (; i < n; i++) {
        found |= p(X{x[i]});
    }
    return found != 0;
}

//
// The fns, element by element
//

// The unsigned type T's wrapping arithmetic is done in: at least unsigned
// int, so that narrower types' promotion to int can't overflow
template <typename T>
using wrap_t = std::conditional_t<
    (sizeof(T) < sizeof(unsigned)), unsigned, std::make_unsigned_t<T>>;

struct AddF
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return static_cast<T>(wrap_t<T>(a) + wrap_t<T>(b));
    }
};

struct SubF
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return static_cast<T>(wrap_t<T>(a) - wrap_t<T>(b));
    }
};

struct MulF
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return static_cast<T>(wrap_t<T>(a) * wrap_t<T>(b));
    }
};

struct MinF
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return std::min(a, b);
    }
};

struct MaxF
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return std::max(a, b);
    }
};

struct LtF
{
    template <typename T>
    uint8_t operator()(T const a, T const b) const
    {
        return a < b;
    }
};

struct LeF
{
    template <typename T>
    uint8_t operator()(T const a, T const b) const
    {
        return a <= b;
    }
};

struct EqF
{
    template <typename T>
    uint8_t operator()(T const a, T const b) const
    {
        return a == b;
    }
};

// As a mask, all ones where c isn't 0: GCC leaves `c ? a : b` scalar for
// int64 values with the uint8 condition, but vectorizes this
struct WhereF
{
    template <typename T>
    T operator()(uint8_t const c, T const a, T const b) const
    {
        using U = std::make_unsigned_t<T>;
        auto const mask = static_cast<U>(U{0} - U{c != 0});
        return static_cast<T>(
            (static_cast<U>(a) & mask) | (static_cast<U>(b) & ~mask));
    }
};

// Clamps to To's range, then converts. The bounds are taken in T, where they
// clamp to T's own range, so the comparisons are of one type
template <typename To>
struct SaturateF
{
    template <typename T>
    To operator()(T const x) const
    {
        using To_limits = std::numeric_limits<To>;
        using T_limits = std::numeric_limits<T>;
        constexpr T lo = std::cmp_less(To_limits::min(), T_limits::min())
                             ? T_limits::min()
                             : static_cast<T>(To_limits::min());
        constexpr T hi = std::cmp_greater(To_limits::max(), T_limits::max())
                             ? T_limits::max()
                             : static_cast<T>(To_limits::max());
        return static_cast<To>(std::clamp(x, lo, hi));
    }
};

// Divc by a power of two, 2^shift, for a shift less than T's width: a shift,
// which vectorizes, with 2^shift - 1 added to a negative signed x first, so
// that it rounds toward zero, as the division does. The sum can't overflow T
template <typename T>
struct DivcPow2F
{
    unsigned shift;

    T operator()(T const x) const
    {
        if constexpr (std::is_signed_v<T>) {
            T const bias = static_cast<T>((wrap_t<T>{1} << shift) - 1);
            return static_cast<T>((x < 0 ? x + bias : x) >> shift);
        }
        else {
            return static_cast<T>(x >> shift);
        }
    }
};

// Divc by any unsigned divisor but 0, which the validator rejects, truncating
// toward zero. A signed x is divided by its magnitude, then the quotient gets
// x's sign back: |quotient| <= |x|, so it fits T. All of it is in uint64_t,
// so nothing overflows, including for T's minimum or a divisor of 2^63 or
// more. Scalar: x86 has no vector integer division
template <typename T>
struct DivcF
{
    uint64_t divisor;

    T operator()(T const x) const
    {
        if constexpr (std::is_signed_v<T>) {
            uint64_t const magnitude =
                x < 0 ? uint64_t{0} - static_cast<uint64_t>(x)
                      : static_cast<uint64_t>(x);
            uint64_t const quotient = magnitude / divisor;
            return static_cast<T>(x < 0 ? uint64_t{0} - quotient : quotient);
        }
        else {
            return static_cast<T>(static_cast<uint64_t>(x) / divisor);
        }
    }
};

// Div, QMul, QDiv, QExp and QInvSqrt as fixed_point.hpp computes them; Div is
// QDiv with 0 fractional bits
struct QMulF
{
    unsigned bits;

    template <typename T>
    T operator()(T const a, T const b) const
    {
        return q_mul(a, b, bits);
    }
};

struct QDivF
{
    unsigned bits;

    template <typename T>
    T operator()(T const a, T const b) const
    {
        return q_div(a, b, bits);
    }
};

struct QExpF
{
    unsigned bits;

    template <typename T>
    T operator()(T const x) const
    {
        return q_exp(x, bits);
    }
};

struct QInvSqrtF
{
    unsigned bits;

    template <typename T>
    T operator()(T const x) const
    {
        return q_inv_sqrt(x, bits);
    }
};

struct ISqrtF
{
    template <typename T>
    T operator()(T const x) const
    {
        return floor_sqrt(x);
    }
};

struct IsZero
{
    template <typename T>
    bool operator()(T const x) const
    {
        return x == 0;
    }
};

struct IsNegative
{
    template <typename T>
    bool operator()(T const x) const
    {
        return x < 0;
    }
};

//
// Running one fn on a chunk
//

// Copies the first element at `data`, of `element_size` bytes, to the
// elements after it, up to `n`: a uniform value across a chunk. `data` is a
// register's block or a chunk of the output, so it's aligned
void fill_uniform(
    uint8_t *const data, size_t const element_size, size_t const n)
{
    if (n <= 1) {
        return;
    }
    auto const fill = [&]<typename T>() {
        T *const elements = reinterpret_cast<T *>(data);
        std::fill_n(elements + 1, n - 1, elements[0]);
    };
    switch (element_size) {
    case 1:
        return fill.operator()<uint8_t>();
    case 2:
        return fill.operator()<uint16_t>();
    case 4:
        return fill.operator()<uint32_t>();
    case 8:
        return fill.operator()<uint64_t>();
    default:
        MONAD_ABORT();
    }
}

// Where a fn writes, and how many elements: all the chunk's, or one, for a
// fn whose operands are all uniform
struct FnOutput
{
    uint8_t *data;
    size_t n;
};

template <typename Out, typename X, typename F>
[[gnu::always_inline]] inline void
apply1(ScalarRegister const &x, FnOutput const &out, F const f)
{
    map1<Out, X>(as_elements<X>(x.data), as_elements<Out>(out.data), out.n, f);
}

template <typename Out, typename X, typename Y, typename F>
[[gnu::always_inline]] inline void apply2(
    ScalarRegister const &x, ScalarRegister const &y, FnOutput const &out,
    F const f)
{
    map2<Out, X, Y>(
        as_elements<X>(x.data),
        as_elements<Y>(y.data),
        as_elements<Out>(out.data),
        out.n,
        f);
}

template <typename X, typename P>
[[gnu::always_inline]] inline bool
check(ScalarRegister const &x, size_t const n, P const p)
{
    return any_of<X>(as_elements<X>(x.data), n, p);
}

// A fn's result's dtype, or the error it fails with: a plain struct rather
// than a Result, as one is returned for every fn on every chunk
struct FnResult
{
    Dtype dtype;
    GraphEvalError error;
};

// Runs fn Fn, whose params and operands are given, into `out`
template <FineFn Fn>
FnResult run_fn(
    [[maybe_unused]] FnParams<Fn> const &params,
    std::array<ScalarRegister const *, FnArity<Fn>> const &args,
    FnOutput const &out)
{
    ScalarRegister const &a = *args[0];
    if constexpr (Fn == FineFn::Where) {
        // Operands: condition, then the values, of the result's dtype
        ScalarRegister const &x = *args[1];
        ScalarRegister const &y = *args[2];
        // It only moves bits, so it runs on the signed type of the values'
        // width: GCC vectorizes WhereF for int64 but not for uint64
        visit_dtype(x.dtype, [&]<typename T>() {
            using S = std::make_signed_t<T>;
            map3<S, uint8_t, S, S>(
                as_elements<uint8_t>(a.data),
                as_elements<S>(x.data),
                as_elements<S>(y.data),
                as_elements<S>(out.data),
                out.n,
                WhereF{});
        });
        return {x.dtype, GraphEvalError::Success};
    }
    else if constexpr (Fn == FineFn::Saturate) {
        Dtype const to = params;
        visit_dtype(a.dtype, [&]<typename T>() {
            visit_dtype(to, [&]<typename To>() {
                apply1<To, T>(a, out, SaturateF<To>{});
            });
        });
        return {to, GraphEvalError::Success};
    }
    else {
        return visit_dtype(a.dtype, [&]<typename T>() -> FnResult {
            if constexpr (Fn == FineFn::Add) {
                apply2<T, T, T>(a, *args[1], out, AddF{});
            }
            else if constexpr (Fn == FineFn::Sub) {
                apply2<T, T, T>(a, *args[1], out, SubF{});
            }
            else if constexpr (Fn == FineFn::Mul) {
                apply2<T, T, T>(a, *args[1], out, MulF{});
            }
            else if constexpr (Fn == FineFn::Min) {
                apply2<T, T, T>(a, *args[1], out, MinF{});
            }
            else if constexpr (Fn == FineFn::Max) {
                apply2<T, T, T>(a, *args[1], out, MaxF{});
            }
            else if constexpr (Fn == FineFn::Lt) {
                apply2<uint8_t, T, T>(a, *args[1], out, LtF{});
                return {Dtype::uint8, GraphEvalError::Success};
            }
            else if constexpr (Fn == FineFn::Le) {
                apply2<uint8_t, T, T>(a, *args[1], out, LeF{});
                return {Dtype::uint8, GraphEvalError::Success};
            }
            else if constexpr (Fn == FineFn::Eq) {
                apply2<uint8_t, T, T>(a, *args[1], out, EqF{});
                return {Dtype::uint8, GraphEvalError::Success};
            }
            else if constexpr (Fn == FineFn::Divc) {
                uint64_t const divisor = params;
                if (std::has_single_bit(divisor)) {
                    auto const shift =
                        static_cast<unsigned>(std::countr_zero(divisor));
                    if (shift >= 8 * sizeof(T)) {
                        // |x| < 2^shift, so every quotient is 0, and a shift
                        // by T's width or more is undefined
                        std::memset(out.data, 0, out.n * sizeof(T));
                    }
                    else {
                        apply1<T, T>(a, out, DivcPow2F<T>{shift});
                    }
                }
                else {
                    apply1<T, T>(a, out, DivcF<T>{divisor});
                }
            }
            else if constexpr (Fn == FineFn::Div || Fn == FineFn::QDiv) {
                if (check<T>(*args[1], out.n, IsZero{})) {
                    return {a.dtype, GraphEvalError::DivisionByZero};
                }
                unsigned bits = 0;
                if constexpr (Fn == FineFn::QDiv) {
                    bits = params;
                }
                apply2<T, T, T>(a, *args[1], out, QDivF{bits});
            }
            else if constexpr (Fn == FineFn::QMul) {
                apply2<T, T, T>(a, *args[1], out, QMulF{params});
            }
            else if constexpr (Fn == FineFn::QExp) {
                apply1<T, T>(a, out, QExpF{params});
            }
            else if constexpr (Fn == FineFn::QInvSqrt) {
                if (check<T>(a, out.n, IsZero{})) {
                    return {a.dtype, GraphEvalError::DivisionByZero};
                }
                if constexpr (std::is_signed_v<T>) {
                    if (check<T>(a, out.n, IsNegative{})) {
                        return {a.dtype, GraphEvalError::DomainError};
                    }
                }
                apply1<T, T>(a, out, QInvSqrtF{params});
            }
            else if constexpr (Fn == FineFn::ISqrt) {
                if constexpr (std::is_unsigned_v<T>) {
                    apply1<T, T>(a, out, ISqrtF{});
                }
                else {
                    // The validator allows ISqrt on unsigned dtypes only
                    MONAD_ABORT();
                }
            }
            else {
                static_assert(false, "a fn without a kernel");
            }
            return {a.dtype, GraphEvalError::Success};
        });
    }
}

// FAdd: Add, as a loop of AVX-512 intrinsics rather than map2, and inlined
// into run_scalar rather than reached through run_fn. Wrapping addition gives
// the same bits for a signed and an unsigned dtype, so only the lanes' width
// matters. Each 64-byte block is loaded before it's stored, so the output may
// be one of the operands, and no __restrict is needed. A last, partial block
// is loaded and stored under a byte mask, which touches no byte outside the
// chunk. Without AVX-512BW, FAdd runs Add's kernel
#if defined(__AVX512BW__)
template <size_t Bytes>
[[gnu::always_inline]] inline __m512i
add_lanes(__m512i const a, __m512i const b)
{
    if constexpr (Bytes == 1) {
        return _mm512_add_epi8(a, b);
    }
    else if constexpr (Bytes == 2) {
        return _mm512_add_epi16(a, b);
    }
    else if constexpr (Bytes == 4) {
        return _mm512_add_epi32(a, b);
    }
    else {
        return _mm512_add_epi64(a, b);
    }
}

template <size_t Bytes>
[[gnu::always_inline]] inline void fadd_bytes(
    uint8_t const *const x, uint8_t const *const y, uint8_t *const out,
    size_t const n_bytes)
{
    size_t i = 0;
    for (; i + 64 <= n_bytes; i += 64) {
        __m512i const a = _mm512_loadu_si512(x + i);
        __m512i const b = _mm512_loadu_si512(y + i);
        _mm512_storeu_si512(out + i, add_lanes<Bytes>(a, b));
    }
    if (i < n_bytes) {
        __mmask64 const k = (uint64_t{1} << (n_bytes - i)) - 1;
        __m512i const a = _mm512_maskz_loadu_epi8(k, x + i);
        __m512i const b = _mm512_maskz_loadu_epi8(k, y + i);
        _mm512_mask_storeu_epi8(out + i, k, add_lanes<Bytes>(a, b));
    }
}
#endif

[[gnu::always_inline]] inline FnResult
fadd(ScalarRegister const &x, ScalarRegister const &y, FnOutput const &out)
{
#if defined(__AVX512BW__)
    size_t const n_bytes = out.n * dtype_size(x.dtype);
    switch (dtype_size(x.dtype)) {
    case 1:
        fadd_bytes<1>(x.data, y.data, out.data, n_bytes);
        break;
    case 2:
        fadd_bytes<2>(x.data, y.data, out.data, n_bytes);
        break;
    case 4:
        fadd_bytes<4>(x.data, y.data, out.data, n_bytes);
        break;
    default:
        fadd_bytes<8>(x.data, y.data, out.data, n_bytes);
        break;
    }
    return {x.dtype, GraphEvalError::Success};
#else
    return run_fn<FineFn::Add>({}, {&x, &y}, out);
#endif
}

//
// A Scalar node's inputs
//

// How an input gives a chunk its elements
enum class InputKind : uint8_t
{
    Direct, // The output's shape: the input's own data, at the chunk's offset
    Uniform, // One element: copied across the block once a node
    Expand, // Broadcast: the chunk's elements, copied into the block each chunk
};

struct ScalarInput
{
    InputKind kind;
    uint8_t const *data;
    size_t element_size;
    // For Expand: the output's dimensions as this input sees them, and the
    // input's element stride along each, 0 where it broadcasts. Dimensions of
    // size 1 are left out, and adjacent ones merged where the input steps
    // through them as through one, so that runs along the last are as long as
    // they can be: [1, 4, 35] broadcast to [128, 4, 35] is [128, 140] with
    // strides [0, 1], a run of 140 elements a row rather than 35
    size_t rank;
    std::array<uint64_t, MAX_RANK> dims;
    std::array<uint64_t, MAX_RANK> strides;
    // For Expand: the index the next chunk starts at, in those dimensions,
    // and the input offset of that index's row (every dimension but the
    // last). Chunks run in order, so each carries on from where the last one
    // stopped
    std::array<uint64_t, MAX_RANK> index;
    uint64_t row;
};

// A broadcast input's dimensions and strides, merged, from its broadcast to
// `shape`. It has more than one element and fewer than the output, so at
// least one dimension is left
void merge_dimensions(
    ScalarInput &input, Shape const &shape, BroadcastLoop const &loop)
{
    input.rank = 0;
    for (size_t d = 0; d < shape.rank(); d++) {
        uint64_t const dim = shape.dimensions()[d];
        uint64_t const stride = loop.strides[d];
        if (dim == 1) {
            continue;
        }
        if (input.rank > 0 && input.strides[input.rank - 1] == stride * dim) {
            input.dims[input.rank - 1] *= dim;
            input.strides[input.rank - 1] = stride;
        }
        else {
            input.dims[input.rank] = dim;
            input.strides[input.rank] = stride;
            input.rank++;
        }
    }
    MONAD_DEBUG_ASSERT(input.rank > 0);
    input.index = {};
    input.row = 0;
}

// Copies the elements of `input` that the next `n` output elements read
// into `out`, a register's block, a run along the output's last dimension at
// a time: a copy if the input runs along it too, else a repeat of one
// element, and moves the input's index past them. E is an unsigned type of
// the element's size, so the copies and repeats are of typed elements
template <typename E>
void expand_elements(
    ScalarInput &input, size_t const n, uint8_t *const out_bytes)
{
    size_t const rank = input.rank;
    auto const &dims = input.dims;
    auto const *const in = as_elements<E>(input.data);
    E *const out = reinterpret_cast<E *>(out_bytes);
    auto const &strides = input.strides;
    auto &index = input.index;
    uint64_t const last_dim = dims[rank - 1];
    uint64_t const last_stride = strides[rank - 1];
    size_t done = 0;
    while (done < n) {
        uint64_t const offset = input.row + index[rank - 1] * last_stride;
        auto const run = static_cast<size_t>(
            std::min<uint64_t>(last_dim - index[rank - 1], n - done));
        if (last_stride != 0) {
            std::memcpy(out + done, in + offset, run * sizeof(E));
        }
        else {
            std::fill_n(out + done, run, E{in[offset]});
        }
        done += run;
        index[rank - 1] += run;
        if (index[rank - 1] < last_dim) {
            // The chunk ended inside this row; the next one carries on in it
            break;
        }
        // On to the next row
        index[rank - 1] = 0;
        for (size_t d = rank - 1; d-- > 0;) {
            input.row += strides[d];
            if (++index[d] < dims[d]) {
                break;
            }
            input.row -= dims[d] * strides[d];
            index[d] = 0;
        }
    }
}

void expand_chunk(ScalarInput &input, size_t const n, uint8_t *const out)
{
    switch (input.element_size) {
    case 1:
        return expand_elements<uint8_t>(input, n, out);
    case 2:
        return expand_elements<uint16_t>(input, n, out);
    case 4:
        return expand_elements<uint32_t>(input, n, out);
    case 8:
        return expand_elements<uint64_t>(input, n, out);
    default:
        MONAD_ABORT();
    }
}

// Moves `code` past `n_fns` fns, without running them: for a node with no
// elements, where no chunk's walk finds where the program ends
void skip_fns(uint8_t const *&code, size_t const n_fns)
{
    for (size_t i = 0; i < n_fns; i++) {
        visit_fn(take<FineFn>(code), [&]<FineFn Fn>() {
            (void)take_params<Fn>(code);
            skip_bytes(code, FnArity<Fn> + (i + 1 < n_fns ? 1 : 0));
        });
    }
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

FineInterpreter::FineInterpreter(
    Finecode const &finecode, State &state,
    std::span<TensorInput const> const inputs, uint8_t *const arena)
    : finecode_(finecode)
    , state_(state)
    , inputs_(inputs)
    , arena_(arena)
{
}

Tensor FineInterpreter::node(size_t const id) const
{
    uint32_t const location = finecode_.node_location(id);
    uint8_t const *const data =
        (location & FINE_CODE_LOCATION)
            ? finecode_.ops() + (location & ~FINE_CODE_LOCATION)
            : arena_ + location;
    return Tensor{finecode_.node_type(id), const_cast<uint8_t *>(data)};
}

// The call's inputs must have the graph's input types
Result<void> FineInterpreter::check_inputs() const
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
    return outcome::success();
}

// Copies each input into the arena, in host byte order
Result<void> FineInterpreter::load_inputs()
{
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
    }
    return outcome::success();
}

Result<void> FineInterpreter::run_scalar(
    uint8_t const *&code, size_t const id, ScalarRegisters &file)
{
    Tensor const output = node(id);
    Shape const &shape = output.type().shape();
    uint64_t const size = shape.size();
    size_t const output_element_size = dtype_size(output.type().dtype());
    auto &registers = file.registers;
    // The elements of the longest chunk, which a uniform input or constant
    // is copied across once
    auto const longest =
        static_cast<size_t>(std::min<uint64_t>(SCALAR_CHUNK, size));

    // The inputs: registers 0 to n_inputs - 1
    skip<Shape>(code);
    size_t const n_inputs = take<uint8_t>(code);
    std::array<ScalarInput, MAX_SCALAR_INPUTS> inputs;
    for (size_t i = 0; i < n_inputs; i++) {
        Tensor const tensor = node(take<uint16_t>(code));
        TensorType const &type = tensor.type();
        ScalarInput &input = inputs[i];
        input.data = tensor.data();
        input.element_size = dtype_size(type.dtype());
        registers[i].dtype = type.dtype();
        if (type.shape().size() == size) {
            input.kind = InputKind::Direct;
            registers[i].uniform = false;
        }
        else if (type.shape().size() == 1) {
            input.kind = InputKind::Uniform;
            std::memcpy(file.blocks[i], input.data, input.element_size);
            fill_uniform(file.blocks[i], input.element_size, longest);
            registers[i] = {file.blocks[i], true, type.dtype()};
        }
        else {
            input.kind = InputKind::Expand;
            // It broadcast at validation, so this can't fail
            merge_dimensions(
                input, shape, type.shape().broadcast_to(shape).assume_value());
            registers[i] = {file.blocks[i], false, type.dtype()};
        }
    }

    // The constants: the next registers, each uniform
    size_t const n_constants = take<uint8_t>(code);
    for (size_t i = n_inputs; i < n_inputs + n_constants; i++) {
        auto const dtype = take<Dtype>(code);
        size_t const element_size = dtype_size(dtype);
        std::memcpy(file.blocks[i], code, element_size);
        skip_bytes(code, element_size);
        fill_uniform(file.blocks[i], element_size, longest);
        registers[i] = {file.blocks[i], true, dtype};
    }

    // The fns, run on each chunk in turn. Every chunk's walk through them
    // ends where the program does, which is where `code` goes on from; with
    // no elements, no chunk runs, so the program is walked just to find that
    size_t const n_fns = take<uint8_t>(code);
    uint8_t const *const program = code;
    if (size == 0) {
        skip_fns(code, n_fns);
        return outcome::success();
    }

    for (uint64_t start = 0; start < size; start += SCALAR_CHUNK) {
        auto const n =
            static_cast<size_t>(std::min<uint64_t>(SCALAR_CHUNK, size - start));
        for (size_t i = 0; i < n_inputs; i++) {
            ScalarInput &input = inputs[i];
            if (input.kind == InputKind::Direct) {
                registers[i].data = input.data + start * input.element_size;
            }
            else if (input.kind == InputKind::Expand) {
                expand_chunk(input, n, file.blocks[i]);
            }
        }

        // Each fn writes its destination register's block, or the last one
        // the output's chunk. One whose operands are all uniform runs on one
        // element, which is then copied across the chunk. The per-fn lambda
        // is always inlined: left to itself, GCC inlines some of the 17 and
        // calls the rest, as run_scalar reaches --param large-function-growth
        uint8_t const *pc = program;
        for (size_t f = 0; f < n_fns; f++) {
            bool const last = f + 1 == n_fns;
            GraphEvalError error = visit_fn(
                take<FineFn>(pc),
                [&]<FineFn Fn>() __attribute__((always_inline)) {
                    [[maybe_unused]] auto const params = take_params<Fn>(pc);
                    std::array<ScalarRegister const *, FnArity<Fn>> args;
                    bool uniform = true;
                    for (size_t a = 0; a < FnArity<Fn>; a++) {
                        args[a] = &registers[take<uint8_t>(pc)];
                        uniform &= args[a]->uniform;
                    }
                    size_t const dst = last ? 0 : take<uint8_t>(pc);
                    uint8_t *const data =
                        last ? output.data() + start * output_element_size
                             : file.blocks[dst];
                    FnOutput const out{data, uniform ? size_t{1} : n};
                    FnResult const result =
                        [&]() __attribute__((always_inline)) -> FnResult {
                        if constexpr (Fn == FineFn::FAdd) {
                            return fadd(*args[0], *args[1], out);
                        }
                        else {
                            return run_fn<Fn>(params, args, out);
                        }
                    }();
                    if (result.error != GraphEvalError::Success) {
                        return result.error;
                    }
                    if (uniform) {
                        fill_uniform(data, dtype_size(result.dtype), n);
                    }
                    if (!last) {
                        registers[dst] = {data, uniform, result.dtype};
                    }
                    return GraphEvalError::Success;
                });
            if (error != GraphEvalError::Success) {
                return error;
            }
        }
        code = pc;
    }
    return outcome::success();
}

MONAD_GRAPH_EVAL_NAMESPACE_END

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

//
// The other ops, reading their inputs at any address, as a Literal's are.
// Their outputs are in the arena, aligned
//

// A shape's elements before, along and after an axis
struct AxisSplit
{
    uint64_t outer;
    uint64_t length;
    uint64_t inner;
};

AxisSplit split_at(Shape const &shape, size_t const axis)
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

// The inputs joined along an axis, in order. Each input has out's dimensions
// except along the axis, so for each coordinate before the axis, out's
// elements are each input's elements in turn, each a contiguous block
void concat(
    std::span<Tensor const> const inputs, size_t const axis, Tensor &out)
{
    // With no elements there is nothing to copy, and the dimensions before
    // the axis can multiply to more blocks than a loop could step through
    if (out.type().shape().size() == 0) {
        return;
    }
    size_t const size = dtype_size(out.type().dtype());
    AxisSplit const s = split_at(out.type().shape(), axis);
    uint8_t *dst = out.data();
    for (uint64_t o = 0; o < s.outer; o++) {
        for (Tensor const &x : inputs) {
            uint64_t const block =
                uint64_t{x.type().shape().dimensions()[axis]} * s.inner * size;
            std::memcpy(dst, x.data() + o * block, block);
            dst += block;
        }
    }
}

// Transpose's view of its input, [outer, a, middle, b, inner], with a and b
// the dimensions along the lower and the higher of the two axes. Its output
// is [outer, b, middle, a, inner]
struct TransposeSplit
{
    uint64_t outer;
    uint64_t a;
    uint64_t middle;
    uint64_t b;
    uint64_t inner;
};

// x's element (o, i, m, j, k) is out's (o, j, m, i, k). For each o, j and m,
// out's elements for every i and k are contiguous, and x's are `a` blocks of
// inner contiguous elements, middle * b * inner elements apart: each block is
// copied whole, or, for inner 1, as one element. E is an unsigned type of the
// element's size
template <typename E>
void transpose_elements(
    uint8_t const *const x_bytes, uint8_t *const out_bytes,
    TransposeSplit const &s)
{
    auto const *const x = as_elements<E>(x_bytes);
    E *const out = reinterpret_cast<E *>(out_bytes);
    uint64_t const step = s.middle * s.b * s.inner;
    for (uint64_t o = 0; o < s.outer; o++) {
        for (uint64_t j = 0; j < s.b; j++) {
            for (uint64_t m = 0; m < s.middle; m++) {
                E *const dst =
                    out + ((o * s.b + j) * s.middle + m) * s.a * s.inner;
                auto const *const src =
                    x + ((o * s.a * s.middle + m) * s.b + j) * s.inner;
                if (s.inner == 1) {
                    for (uint64_t i = 0; i < s.a; i++) {
                        dst[i] = src[i * step];
                    }
                }
                else {
                    for (uint64_t i = 0; i < s.a; i++) {
                        std::memcpy(
                            dst + i * s.inner,
                            src + i * step,
                            s.inner * sizeof(E));
                    }
                }
            }
        }
    }
}

// x with dimensions axis0 and axis1 swapped; with equal axes, a copy of x
void transpose(
    Tensor const &x, size_t const axis0, size_t const axis1, Tensor &out)
{
    TensorType const &type = x.type();
    if (axis0 == axis1) {
        std::memcpy(out.data(), x.data(), type.size_bytes());
        return;
    }
    // With no elements there's nothing to copy, and the loops would still
    // step through the dimensions other than the one of 0, whose product can
    // be far more than any tensor's elements
    if (type.shape().size() == 0) {
        return;
    }
    size_t const lo = std::min(axis0, axis1);
    size_t const hi = std::max(axis0, axis1);
    auto const &dims = type.shape().dimensions();
    TransposeSplit s{1, dims[lo], 1, dims[hi], 1};
    for (size_t d = 0; d < lo; d++) {
        s.outer *= dims[d];
    }
    for (size_t d = lo + 1; d < hi; d++) {
        s.middle *= dims[d];
    }
    for (size_t d = hi + 1; d < type.shape().rank(); d++) {
        s.inner *= dims[d];
    }
    switch (dtype_size(type.dtype())) {
    case 1:
        return transpose_elements<uint8_t>(x.data(), out.data(), s);
    case 2:
        return transpose_elements<uint16_t>(x.data(), out.data(), s);
    case 4:
        return transpose_elements<uint32_t>(x.data(), out.data(), s);
    case 8:
        return transpose_elements<uint64_t>(x.data(), out.data(), s);
    default:
        MONAD_ABORT();
    }
}

// IndexError unless every index is in [0, length); then out's slices are
// copied from x's
Result<void>
gather(Tensor const &x, Tensor const &indices, size_t const axis, Tensor &out)
{
    size_t const size = dtype_size(x.type().dtype());
    AxisSplit const xs = split_at(x.type().shape(), axis);
    uint64_t const slice = xs.inner * size;
    uint64_t const count = indices.type().shape().size();
    return visit_dtype(
        indices.type().dtype(), [&]<typename I>() -> Result<void> {
            auto const *const index = as_elements<I>(indices.data());
            for (uint64_t k = 0; k < count; k++) {
                if (std::cmp_less(I{index[k]}, 0) ||
                    std::cmp_greater_equal(I{index[k]}, xs.length)) {
                    return GraphEvalError::IndexError;
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
            return outcome::success();
        });
}

// out[i] = f(prev[i], x[i]): a row of CumSum, from the row before
template <typename T, typename F>
[[gnu::noinline]] void combine_row(
    T const *__restrict const prev, unaligned_t<T> const *__restrict const x,
    T *__restrict const out, uint64_t const n, F const f)
{
    for (uint64_t i = 0; i < n; i++) {
        out[i] = f(prev[i], T{x[i]});
    }
}

// acc[i] = f(acc[i], x[i]): a row into a reduction's result
template <typename T, typename F>
[[gnu::noinline]] void accumulate_row(
    T *__restrict const acc, unaligned_t<T> const *__restrict const x,
    uint64_t const n, F const f)
{
    for (uint64_t i = 0; i < n; i++) {
        acc[i] = f(acc[i], T{x[i]});
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
                    combine_row(
                        outs + at - s.inner,
                        xs + at,
                        outs + at,
                        s.inner,
                        AddF{});
                }
            }
        }
    });
}

// The reduction of n > 0 consecutive elements. For a 64-bit T, in a
// vector's worth of independent lanes, combined at the end: GCC leaves a
// reduction into one 64-bit accumulator scalar (FINDINGS.md). For narrower
// ones a plain loop, which GCC vectorizes with its accumulator in a
// register, where it keeps an array of 32-bit lanes on the stack, which made
// mnist's int32 ReduceSum slower. Wrapping addition and max give the same
// result in any order
template <typename T, typename F>
[[gnu::noinline]] T reduce_contiguous(
    unaligned_t<T> const *__restrict const x, uint64_t const n, F const f)
{
    constexpr size_t L = SCALAR_VECTOR / sizeof(T);
    uint64_t i = 0;
    T result = x[0];
    if (sizeof(T) == 8 && n >= 2 * L) {
        T lanes[L];
        for (size_t j = 0; j < L; j++) {
            lanes[j] = x[j];
        }
        for (i = L; i + L <= n; i += L) {
            for (size_t j = 0; j < L; j++) {
                lanes[j] = f(lanes[j], T{x[i + j]});
            }
        }
        result = lanes[0];
        for (size_t j = 1; j < L; j++) {
            result = f(result, lanes[j]);
        }
    }
    else {
        i = 1;
    }
    for (; i < n; i++) {
        result = f(result, T{x[i]});
    }
    return result;
}

// ReduceSum (wrapping) or ReduceMax along an axis, which keeps length 1. The
// validator rejects an empty axis. With one element a row (every dimension
// after the axis is 1), each of the outer blocks is a contiguous run, reduced
// in one call rather than a row of one element at a time
template <typename F>
void reduce(Tensor const &x, size_t const axis, Tensor &out, F const f)
{
    AxisSplit const s = split_at(x.type().shape(), axis);
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        auto const *const xs = as_elements<T>(x.data());
        T *const outs = reinterpret_cast<T *>(out.data());
        for (uint64_t o = 0; o < s.outer; o++) {
            auto const *const rows = xs + o * s.length * s.inner;
            T *const result = outs + o * s.inner;
            if (s.inner == 1) {
                *result = reduce_contiguous<T>(rows, s.length, f);
                continue;
            }
            std::memcpy(result, rows, s.inner * sizeof(T));
            for (uint64_t r = 1; r < s.length; r++) {
                accumulate_row(result, rows + r * s.inner, s.inner, f);
            }
        }
    });
}

// ArgMin or ArgMax along an axis, which keeps length 1. Each element of out, a
// uint16_t, is for one choice of the coordinates other than the axis: the
// smallest index i along the axis such that `better` prefers no element along
// the axis to element i. With `better` as <, that is the index of the first
// smallest element; as >, of the first largest. The validator rejects an
// empty axis, so every index is below the length along it, at most 65535.
// Each outer block's rows are read in order, each element compared with the
// best so far at its position, which is read from x at the index out holds
// for that position. With one element a row (every dimension after the axis
// is 1), each outer block is a contiguous run, scanned with its best value in
// a local
template <typename Better>
void arg_extreme(
    Tensor const &x, size_t const axis, Tensor &out, Better const better)
{
    // With no elements there is nothing to write, and the dimensions other
    // than the one of 0 can multiply to more rows than a loop could step
    // through
    if (out.type().shape().size() == 0) {
        return;
    }
    AxisSplit const s = split_at(x.type().shape(), axis);
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        auto const *const xs = as_elements<T>(x.data());
        auto *const outs = reinterpret_cast<uint16_t *>(out.data());
        for (uint64_t o = 0; o < s.outer; o++) {
            auto const *const rows = xs + o * s.length * s.inner;
            uint16_t *const best = outs + o * s.inner;
            if (s.inner == 1) {
                uint64_t index = 0;
                T value = rows[0];
                for (uint64_t r = 1; r < s.length; r++) {
                    if (better(T{rows[r]}, value)) {
                        index = r;
                        value = rows[r];
                    }
                }
                *best = static_cast<uint16_t>(index);
                continue;
            }
            std::memset(best, 0, s.inner * sizeof(uint16_t));
            for (uint64_t r = 1; r < s.length; r++) {
                auto const *const row = rows + r * s.inner;
                for (uint64_t k = 0; k < s.inner; k++) {
                    T const current = rows[uint64_t{best[k]} * s.inner + k];
                    if (better(T{row[k]}, current)) {
                        best[k] = static_cast<uint16_t>(r);
                    }
                }
            }
        }
    });
}


MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void> FineInterpreter::run_op(
    FineOp const op, uint8_t const *&code, size_t const id,
    ScalarRegisters &file)
{
    auto const input = [&] { return node(take<uint16_t>(code)); };
    switch (op) {
    case FineOp::Scalar:
        return run_scalar(code, id, file);
    case FineOp::Literal:
        // In place: its node location is its data in the code
        skip<TensorType>(code);
        skip_bytes(code, finecode_.node_type(id).size_bytes());
        return outcome::success();
    case FineOp::Reshape:
        // A view: its node location is its input's
        skip<Shape>(code);
        skip<uint16_t>(code);
        return outcome::success();
    default:
        break;
    }
    Tensor out = node(id);
    switch (op) {
    case FineOp::TensorRef: {
        skip<TensorType>(code);
        auto const address = take<Address>(code);
        auto const offset = take<uint32_t>(code);
        return load_code_tensor(
            state_, CodeRef{address, offset}, ByteOrder::LittleEndian, out);
    }
    case FineOp::Transpose: {
        auto const axis0 = take<uint8_t>(code);
        auto const axis1 = take<uint8_t>(code);
        transpose(input(), axis0, axis1, out);
        return outcome::success();
    }
    case FineOp::Concat: {
        auto const axis = take<uint8_t>(code);
        size_t const n_inputs = take<uint8_t>(code);
        std::array<Tensor, MAX_CONCAT_INPUTS> inputs;
        for (size_t i = 0; i < n_inputs; i++) {
            inputs[i] = input();
        }
        concat(std::span<Tensor const>{inputs.data(), n_inputs}, axis, out);
        return outcome::success();
    }
    case FineOp::QMatMul: {
        auto const bits = take<uint8_t>(code);
        skip<Dtype>(code); // The output's dtype, which its node type has
        Tensor const x = input();
        Tensor const y = input();
        qmatmul(x, y, bits, out);
        return outcome::success();
    }
    case FineOp::CumSum: {
        auto const axis = take<uint8_t>(code);
        cumsum(input(), axis, out);
        return outcome::success();
    }
    case FineOp::ArgMin: {
        auto const axis = take<uint8_t>(code);
        arg_extreme(input(), axis, out, [](auto const a, auto const b) {
            return a < b;
        });
        return outcome::success();
    }
    case FineOp::ArgMax: {
        auto const axis = take<uint8_t>(code);
        arg_extreme(input(), axis, out, [](auto const a, auto const b) {
            return a > b;
        });
        return outcome::success();
    }
    case FineOp::ReduceSum: {
        auto const axis = take<uint8_t>(code);
        reduce(input(), axis, out, AddF{});
        return outcome::success();
    }
    case FineOp::ReduceMax: {
        auto const axis = take<uint8_t>(code);
        reduce(input(), axis, out, MaxF{});
        return outcome::success();
    }
    case FineOp::Gather: {
        auto const axis = take<uint8_t>(code);
        Tensor const x = input();
        Tensor const indices = input();
        return gather(x, indices, axis, out);
    }
    case FineOp::Scalar:
    case FineOp::Literal:
    case FineOp::Reshape:
        // Handled above
    case FineOp::Invalid:
        break;
    }
    MONAD_ABORT();
}

Result<GraphOutputs> FineInterpreter::run()
{
    if (finecode_.validation_result() != GraphEvalError::Success) {
        return finecode_.validation_result();
    }
    BOOST_OUTCOME_TRY(check_inputs());
    auto const &output_ids = finecode_.output_ids();
    BOOST_OUTCOME_TRY(load_inputs());

    // Every Scalar node's registers, at the same address
    ScalarRegisters file;

    uint8_t const *code = finecode_.ops();
    size_t const n_inputs = finecode_.n_inputs();
    for (size_t i = 0; i < finecode_.n_ops(); i++) {
        BOOST_OUTCOME_TRY(run_op(take<FineOp>(code), code, n_inputs + i, file));
    }

    GraphOutputs outputs;
    outputs.count = output_ids.size();
    for (size_t i = 0; i < output_ids.size(); i++) {
        outputs.tensors[i] = node(output_ids[i]);
    }
    return outputs;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
