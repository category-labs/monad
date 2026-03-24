// Copyright (C) 2025 Category Labs, Inc.
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

// Microbenchmark for calc_min_version().
//
// Compares the original implementation (calling subtrie_min_version(i) per
// iteration, which re-derives the version array base pointer via three chained
// arithmetic steps — popcount + multiply — on each call) against the optimized
// one (child_min_version_data() called once before the loop as a span).
//
// Creates nodes with 1, 4, 8, and 16 children and measures ns/call.

#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <optional>
#include <span>
#include <vector>

using namespace monad::mpt;

// Original: calls subtrie_min_version(i) each iteration, recomputing base.
static int64_t calc_min_version_original(Node const &node)
{
    int64_t min_version = node.version;
    for (unsigned i = 0; i < node.number_of_children(); ++i) {
        min_version = std::min(min_version, node.subtrie_min_version(i));
    }
    return min_version;
}

// Build a node whose mask has exactly `nchildren` bits set (low bits).
static Node::SharedPtr make_bench_node(unsigned nchildren, int64_t version)
{
    uint16_t const mask = static_cast<uint16_t>((1u << nchildren) - 1u);

    std::vector<ChildData> children(nchildren);
    for (unsigned i = 0; i < nchildren; ++i) {
        children[i].branch = static_cast<uint8_t>(i);
        children[i].subtrie_min_version = version - static_cast<int64_t>(i);
    }

    return make_node(
        mask,
        std::span<ChildData>{children},
        NibblesView{},
        std::nullopt,
        /*data_size=*/0,
        version);
}

template <typename Fn>
static int64_t
run_bench(char const *label, unsigned nchildren, uint64_t iterations, Fn &&fn)
{
    auto const node = make_bench_node(nchildren, 1000);

    // Warm up CPU caches and branch predictor.
    int64_t volatile sink = 0;
    for (uint64_t i = 0; i < 1000; ++i) {
        sink = fn(*node);
    }

    auto const t0 = std::chrono::steady_clock::now();
    for (uint64_t i = 0; i < iterations; ++i) {
        sink = fn(*node);
    }
    auto const t1 = std::chrono::steady_clock::now();
    (void)sink;

    auto const ns =
        std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count();
    auto const per_call = ns / static_cast<int64_t>(iterations);
    std::cout << label << "  children=" << nchildren
              << "  per_call=" << per_call << "ns\n";
    return per_call;
}

int main()
{
    constexpr uint64_t ITERS = 50'000'000;

    std::cout << "--- original (subtrie_min_version(i) per iteration) ---\n";
    for (unsigned const n : {1u, 4u, 8u, 16u}) {
        run_bench("original", n, ITERS, calc_min_version_original);
    }

    std::cout << "\n--- optimized (hoisted base pointer) ---\n";
    for (unsigned const n : {1u, 4u, 8u, 16u}) {
        run_bench("optimized", n, ITERS, calc_min_version);
    }
}
