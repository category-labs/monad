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

#pragma once

#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// The loops of an element-wise op over N operands broadcast together, as
// broadcast_shape broadcasts them
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
    BOOST_OUTCOME_TRY(loops.shape, broadcast_shape(shapes));
    loops.rank = 0;
    Shape const &shape = loops.shape;

    // Each operand's stride along each of the output's dimensions, 0 where
    // it's repeated
    std::array<std::array<uint64_t, 8>, N> strides{};
    for (size_t k = 0; k < N; k++) {
        Shape const &operand = shapes[k];
        uint64_t stride = 1;
        for (size_t i = operand.rank; i-- > 0;) {
            uint16_t const size = operand.dimensions[i];
            if (size != 1) {
                strides[k][shape.rank - operand.rank + i] = stride;
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

MONAD_GRAPH_EVAL_NAMESPACE_END
