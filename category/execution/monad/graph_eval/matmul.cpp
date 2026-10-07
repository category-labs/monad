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

#include <category/core/assert.h>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/matmul.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <immintrin.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <vector>

// Each element of the product is the dot product of a row of x with a column
// of y. The columns are copied out of y 4 at a time into contiguous buffers,
// and each group of copies is used for every row of x before the next is made.
// The dot products then load contiguous vectors, and compute 4 rows by 4
// columns at a time, so that each load of a row or column serves 4 of them.

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// The length of a copy of a column of k elements: k rounded up to whole 64-byte
// vectors, so that the dot products can read whole vectors. The padding is zero
constexpr size_t padded_length(size_t const k)
{
    return (k + 63) / 64 * 64;
}

// Scratch for the copies of 4 columns, as long as columns can be, allocated
// the first time a thread uses it. Its first `size` bytes are zeroed
int8_t *column_scratch(size_t const size)
{
    constexpr size_t max_size =
        4 * padded_length(std::numeric_limits<uint16_t>::max());
    thread_local std::vector<int8_t> scratch(max_size);
    MONAD_DEBUG_ASSERT(size <= max_size);
    std::fill_n(scratch.begin(), size, int8_t{0});
    return scratch.data();
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

// The dot products over k elements of R rows of x, `x_stride` bytes apart,
// with C column copies, `col_stride` bytes apart, into sums[r][c].
//
// vpdpbusd multiplies unsigned bytes by signed ones, adding each 4 products
// into a 32-bit lane, so x's bytes are flipped to x + 128, which is unsigned,
// and the sums are of (x + 128) * y. The caller subtracts the column's
// correction, 128 times its sum. Even with k at its largest, 65535, these sums
// fit in 32 bits.
//
// x's elements past k are masked off, so as not to read past its row or its
// end. They flip to 128, but the column copies' padding is zero
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

// Copies columns n0 to n0 + 3 of y, which is k x n, into cols[c * length + i],
// 16 rows at a time. A 32-bit gather at y[i][n0] fetches y[i][n0..n0+3], one
// row of all four columns, and each column's byte is then split out of the
// words. Columns past n get whatever follows in y, and are never used
void gather_columns(
    int8_t const *const y, size_t const k, size_t const n, size_t const n0,
    int8_t *const cols, size_t const length)
{
    __m512i const offsets = _mm512_mullo_epi32(
        _mm512_setr_epi32(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
        _mm512_set1_epi32(static_cast<int>(n)));
    // A gather reads 4 bytes from each element's address, so only the rows
    // whose words end within y are gathered, the first `gathered`. The rest,
    // in y's last 3 bytes, are copied in scalar below
    uint64_t const y_size = uint64_t{k} * n;
    size_t const gathered =
        y_size < n0 + 4 ? 0 : std::min<uint64_t>(k, (y_size - n0 - 4) / n + 1);
    for (size_t i = 0; i < k; i += 16) {
        __mmask16 const mask =
            i + 16 <= gathered ? __mmask16{0xffff}
            : i < gathered ? static_cast<__mmask16>((1u << (gathered - i)) - 1)
                           : __mmask16{0};
        __m512i const words = _mm512_mask_i32gather_epi32(
            _mm512_setzero_si512(), mask, offsets, y + i * n + n0, 1);
#pragma GCC unroll 4
        for (size_t c = 0; c < 4; c++) {
            _mm_storeu_si128(
                reinterpret_cast<__m128i *>(cols + c * length + i),
                _mm512_cvtepi32_epi8(
                    _mm512_srli_epi32(words, static_cast<unsigned>(8 * c))));
        }
    }
    for (size_t i = gathered; i < k; i++) {
        for (size_t c = 0; c < 4 && n0 + c < n; c++) {
            cols[c * length + i] = y[i * n + n0 + c];
        }
    }
}

// Computes columns n0 to n0 + n_cols - 1 of out, which is m x n, from copies
// of y's columns in cols, 4 rows of x at a time, then the rows left over one
// at a time. Each block computes all 4 copies, but only the first n_cols are
// stored
void multiply_column_group(
    int8_t const *const x, size_t const m, size_t const k, size_t const n,
    int8_t const *const cols, size_t const length, size_t const n0,
    size_t const n_cols, int32_t *const out)
{
    int32_t correction[4];
    for (size_t c = 0; c < n_cols; c++) {
        correction[c] = column_correction(cols + c * length, length);
    }

    size_t i0 = 0;
    for (; i0 + 4 <= m; i0 += 4) {
        int32_t sums[4][4];
        dot_block(x + i0 * k, k, cols, length, k, sums);
        for (size_t r = 0; r < 4; r++) {
            for (size_t c = 0; c < n_cols; c++) {
                out[(i0 + r) * n + n0 + c] = sums[r][c] - correction[c];
            }
        }
    }
    for (; i0 < m; i0++) {
        int32_t sums[1][4];
        dot_block(x + i0 * k, k, cols, length, k, sums);
        for (size_t c = 0; c < n_cols; c++) {
            out[i0 * n + n0 + c] = sums[0][c] - correction[c];
        }
    }
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

void matmul_i8(Tensor const &x, Tensor const &y, Tensor &out)
{
    size_t const m = x.type().shape.dimensions[0];
    size_t const k = x.type().shape.dimensions[1];
    size_t const n = y.type().shape.dimensions[1];
    MONAD_DEBUG_ASSERT(
        x.type().shape.rank == 2 && y.type().shape.rank == 2 &&
        out.type().shape.rank == 2);
    MONAD_DEBUG_ASSERT(y.type().shape.dimensions[0] == k);
    MONAD_DEBUG_ASSERT(
        out.type().shape.dimensions[0] == m &&
        out.type().shape.dimensions[1] == n);

    int8_t const *const x_data = x.elements<int8_t const>().data();
    int8_t const *const y_data = y.elements<int8_t const>().data();
    int32_t *const out_data = out.elements<int32_t>().data();

    size_t const length = padded_length(k);
    int8_t *const cols = column_scratch(4 * length);
    for (size_t n0 = 0; n0 < n; n0 += 4) {
        gather_columns(y_data, k, n, n0, cols, length);
        multiply_column_group(
            x_data,
            m,
            k,
            n,
            cols,
            length,
            n0,
            std::min<size_t>(4, n - n0),
            out_data);
    }
}

MONAD_GRAPH_EVAL_NAMESPACE_END
