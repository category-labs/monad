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

// This file is compiled with -march=znver4, for AVX-512 with VNNI, which every
// validator's CPU has; see category/execution/CMakeLists.txt

#include "category/execution/monad/graph_eval/unaligned.hpp"
#include <category/core/assert.h>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/matmul.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <immintrin.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <type_traits>

// In matmul_i8, each element of the product is the dot product of a row of x
// with a row of y, both contiguous. The dot products load whole vectors from
// the rows, and compute 4 rows of x by 4 rows of y at a time, so that each load
// serves 4 of them.

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// 128 times the sum of a row of y of k elements: what dot_block's sums with it
// are off by. The elements past k are masked off, as in dot_block
int32_t row_correction(int8_t const *const row, size_t const k)
{
    __m512i const flip = _mm512_set1_epi8(static_cast<char>(0x80));
    __m512i acc = _mm512_setzero_si512();
    for (size_t i = 0; i < k; i += 64) {
        __mmask64 const mask =
            k - i >= 64 ? ~__mmask64{0} : (__mmask64{1} << (k - i)) - 1;
        acc = _mm512_dpbusd_epi32(
            acc, flip, _mm512_maskz_loadu_epi8(mask, row + i));
    }
    return _mm512_reduce_add_epi32(acc);
}

// The dot products over k elements of R consecutive rows of x with C
// consecutive rows of y, each row k bytes long, into sums[r][c].
//
// vpdpbusd multiplies unsigned bytes by signed ones, adding each 4 products
// into a 32-bit lane, so x's bytes are flipped to x + 128, which is unsigned,
// and the sums are of (x + 128) * y. The caller subtracts the correction for
// the row of y, 128 times its sum. Even with k at its largest, 65535, these
// sums fit in 32 bits.
//
// The elements past k are masked off, so as not to read past a row or the end
// of x or y. They load as zero: x's then flip to 128, but y's stay zero, so
// their products are zero
template <size_t R, size_t C>
[[gnu::always_inline]] inline void dot_block(
    int8_t const *const x, int8_t const *const y, size_t const k,
    int32_t (&sums)[R][C])
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
                _mm512_maskz_loadu_epi8(mask, x + r * k + i), flip);
        }
#pragma GCC unroll 4
        for (size_t c = 0; c < C; c++) {
            __m512i const row = _mm512_maskz_loadu_epi8(mask, y + c * k + i);
#pragma GCC unroll 4
            for (size_t r = 0; r < R; r++) {
                acc[r][c] = _mm512_dpbusd_epi32(acc[r][c], xs[r], row);
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

// Computes columns j0 to j0 + C - 1 of out, which is m x n, from rows j0 to
// j0 + C - 1 of y, 4 rows of x at a time, then the rows left over one at a
// time
template <size_t C>
void multiply_row_group(
    int8_t const *const x, size_t const m, size_t const k, size_t const n,
    int8_t const *const y, size_t const j0, int32_t *const out)
{
    int8_t const *const rows = y + j0 * k;
    int32_t correction[C];
    for (size_t c = 0; c < C; c++) {
        correction[c] = row_correction(rows + c * k, k);
    }

    size_t i0 = 0;
    for (; i0 + 4 <= m; i0 += 4) {
        int32_t sums[4][C];
        dot_block(x + i0 * k, rows, k, sums);
        for (size_t r = 0; r < 4; r++) {
            for (size_t c = 0; c < C; c++) {
                out[(i0 + r) * n + j0 + c] = sums[r][c] - correction[c];
            }
        }
    }
    for (; i0 < m; i0++) {
        int32_t sums[1][C];
        dot_block(x + i0 * k, rows, k, sums);
        for (size_t c = 0; c < C; c++) {
            out[i0 * n + j0 + c] = sums[0][c] - correction[c];
        }
    }
}

// The signed counterpart of Sum, a uint64_t or unsigned __int128, for a signed
// T, and Sum itself for an unsigned one: the type the sums are shifted in, so
// that a signed one's shift rounds down
template <typename Sum, typename T>
using shift_t = std::conditional_t<
    std::is_signed_v<T>,
    std::conditional_t<sizeof(Sum) == 8, int64_t, __int128>, Sum>;

template <typename Sum, typename T>
using wide_t =
    std::conditional_t<2 * sizeof(T) <= sizeof(Sum), shift_t<Sum, T>, Sum>;

// Each element of out is the dot product of a row of x and a row of y, both
// read contiguously, which GCC vectorizes. For types up to 16 bits wide, the
// products are formed in 32 bits, where they are exact, and a vector holds
// twice as many of them as in 64 bits
template <typename Sum, typename T, typename Out>
[[gnu::noinline]] void qmatmul_any(
    uint8_t const *const x_data, uint8_t const *const y_data, size_t const m,
    size_t const k, size_t const n, unsigned const bits, Out *const out)
{
    using Wide = wide_t<Sum, T>;
    using Product = std::conditional_t<
        sizeof(T) <= 2,
        std::conditional_t<std::is_signed_v<T>, int32_t, uint32_t>,
        Wide>;
    auto const *const x = as_elements<T>(x_data);
    auto const *const y = as_elements<T>(y_data);
    for (size_t i = 0; i < m; i++) {
        for (size_t j = 0; j < n; j++) {
            auto const *__restrict const x_row = x + i * k;
            auto const *__restrict const y_row = y + j * k;
            Sum sum = 0;
            for (size_t p = 0; p < k; p++) {
                auto const product = static_cast<Product>(
                    static_cast<Product>(T{x_row[p]}) *
                    static_cast<Product>(T{y_row[p]}));
                sum += static_cast<Sum>(static_cast<Wide>(product));
            }
            out[i * n + j] =
                static_cast<Out>(static_cast<shift_t<Sum, T>>(sum) >> bits);
        }
    }
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

void matmul_i8(Tensor const &x, Tensor const &y, Tensor &out)
{
    size_t const m = x.type().shape().dimensions()[0];
    size_t const k = x.type().shape().dimensions()[1];
    size_t const n = y.type().shape().dimensions()[0];
    MONAD_DEBUG_ASSERT(
        x.type().shape().rank() == 2 && y.type().shape().rank() == 2 &&
        out.type().shape().rank() == 2);
    MONAD_DEBUG_ASSERT(y.type().shape().dimensions()[1] == k);
    MONAD_DEBUG_ASSERT(
        out.type().shape().dimensions()[0] == m &&
        out.type().shape().dimensions()[1] == n);

    int8_t const *const x_data = x.elements<int8_t const>().data();
    int8_t const *const y_data = y.elements<int8_t const>().data();
    int32_t *const out_data = out.elements<int32_t>().data();

    size_t j0 = 0;
    for (; j0 + 4 <= n; j0 += 4) {
        multiply_row_group<4>(x_data, m, k, n, y_data, j0, out_data);
    }
    // The rows of y left over, fewer than 4, in one group
    switch (n - j0) {
    case 3:
        multiply_row_group<3>(x_data, m, k, n, y_data, j0, out_data);
        break;
    case 2:
        multiply_row_group<2>(x_data, m, k, n, y_data, j0, out_data);
        break;
    case 1:
        multiply_row_group<1>(x_data, m, k, n, y_data, j0, out_data);
        break;
    default:
        break;
    }
}

// The sums wrap at 128 bits, but only their bits from `bits` to `bits` plus
// Out's width reach out, and with `bits` at most 64 those are all below bit
// 128. When they are all below bit 64, summing in 64 bits, wrapping, which
// keeps a sum's low 64 bits exactly, gives the same out, much faster. For types
// up to 16 bits wide, every sum of up to 65535 products is exact in 64 bits
// anyway. Such a sum is below 2^48 in magnitude, so shifting it right by 63
// gives the same 0 or -1 as shifting it by 64, which is undefined for a 64-bit
// integer; the 64-bit path's shift is capped at 63 for that. Otherwise the sums
// are in 128 bits.
//
// With int8 inputs, no shift and an int32 out, every sum is at most 65535 *
// 2^14 in magnitude, below 2^31, so out holds it exactly, and matmul_i8
// computes it with VNNI. Only x's dtype is checked, since y's is the same
void qmatmul(Tensor const &x, Tensor const &y, unsigned const bits, Tensor &out)
{
    if (x.type().dtype() == Dtype::int8 && bits == 0 &&
        out.type().dtype() == Dtype::int32) {
        matmul_i8(x, y, out);
        return;
    }
    size_t const m = x.type().shape().dimensions()[0];
    size_t const k = x.type().shape().dimensions()[1];
    size_t const n = y.type().shape().dimensions()[0];
    visit_dtype(x.type().dtype(), [&]<typename T>() {
        visit_dtype(out.type().dtype(), [&]<typename Out>() {
            Out *const outs = reinterpret_cast<Out *>(out.data());
            if (sizeof(T) <= 2 || bits + 8 * sizeof(Out) <= 64) {
                qmatmul_any<uint64_t, T>(
                    x.data(), y.data(), m, k, n, std::min(bits, 63u), outs);
            }
            else {
                qmatmul_any<unsigned __int128, T>(
                    x.data(), y.data(), m, k, n, bits, outs);
            }
        });
    });
}

MONAD_GRAPH_EVAL_NAMESPACE_END
