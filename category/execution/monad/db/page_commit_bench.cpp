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

// Microbenchmark for monad's page_commit (ISMC over a 4096-byte storage page).
//
// Mirrors the Rust harness in
// category-research-internal/blake3merklebenchmark/src/main.rs:
//   - Same workload generator: place k random 32-byte words in unique pairs
//     (k ≤ 64), spilling extras into already-active pairs for k > 64.
//   - Same pair-count sweep: {1, 2, 4, 8, 16, 32, 40, 48, 56-64, 128}.
//   - Same timing strategy: RDTSC + steady_clock per iteration, 10% warmup,
//     5% trim from each tail, median reported.
//   - CSV output: strategy,page_words,words,pairs,workload,cycles,latency_us.

#include <category/core/bytes.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <random>
#include <vector>

#if defined(__x86_64__)
    #include <x86intrin.h>
#endif

using namespace monad;

namespace
{
    inline uint64_t rdtsc()
    {
#if defined(__x86_64__)
        return __rdtsc();
#else
        return 0;
#endif
    }

    struct timing_stats
    {
        uint64_t median_cycles;
        uint64_t median_nanos;
    };

    template <typename Fn>
    timing_stats benchmark_with_timing(Fn &&fn, size_t const iterations)
    {
        // 10% warmup.
        for (size_t i = 0; i < iterations / 10; ++i) {
            fn();
        }

        std::vector<uint64_t> cycle_samples;
        std::vector<uint64_t> nano_samples;
        cycle_samples.reserve(iterations);
        nano_samples.reserve(iterations);

        for (size_t i = 0; i < iterations; ++i) {
            uint64_t const start_cycles = rdtsc();
            auto const start_time = std::chrono::steady_clock::now();
            fn();
            auto const end_time = std::chrono::steady_clock::now();
            uint64_t const end_cycles = rdtsc();

            cycle_samples.push_back(end_cycles - start_cycles);
            nano_samples.push_back(static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    end_time - start_time)
                    .count()));
        }

        std::sort(cycle_samples.begin(), cycle_samples.end());
        std::sort(nano_samples.begin(), nano_samples.end());

        // Trim 5% from each tail.
        size_t const trim = iterations / 20;
        size_t const lo = trim;
        size_t const hi = iterations - trim;
        size_t const mid = (lo + hi) / 2;

        return timing_stats{
            .median_cycles = cycle_samples[mid],
            .median_nanos = nano_samples[mid],
        };
    }

    // Build a storage_page_t with `num_words` non-zero 32-byte slots.
    // For k ≤ 64, each occupies a unique pair (one word per pair). For k > 64,
    // the extras fill the second word of already-active pairs. Mirrors
    // make_unique_pair_word_page() in the Rust harness.
    storage_page_t build_unique_pair_page(size_t const num_words, uint64_t const seed)
    {
        std::mt19937_64 rng{seed};
        storage_page_t page{};

        size_t const unique = std::min<size_t>(num_words, 64);

        std::vector<uint8_t> chosen_pairs;
        chosen_pairs.reserve(unique);

        std::uniform_int_distribution<uint16_t> pair_dist{0, 63};
        std::uniform_int_distribution<uint16_t> word_dist{0, 1};
        std::uniform_int_distribution<uint16_t> byte_dist{0, 255};

        while (chosen_pairs.size() < unique) {
            uint8_t const pair_idx = static_cast<uint8_t>(pair_dist(rng));
            if (std::find(chosen_pairs.begin(), chosen_pairs.end(), pair_idx) ==
                chosen_pairs.end()) {
                chosen_pairs.push_back(pair_idx);
                uint8_t const word_in_pair = static_cast<uint8_t>(word_dist(rng));
                uint8_t const slot = static_cast<uint8_t>(pair_idx * 2 + word_in_pair);
                for (uint8_t b = 0; b < 32; ++b) {
                    page[slot].bytes[b] = static_cast<uint8_t>(byte_dist(rng));
                }
                page[slot].bytes[0] |= 0x01; // ensure non-zero
            }
        }

        if (num_words > 64) {
            size_t const extra = num_words - 64;
            for (size_t i = 0; i < extra; ++i) {
                uint8_t const pair_idx = chosen_pairs[i];
                uint8_t const slot_left = static_cast<uint8_t>(pair_idx * 2);
                uint8_t const slot_right = static_cast<uint8_t>(pair_idx * 2 + 1);
                for (uint8_t b = 0; b < 32; ++b) {
                    page[slot_left].bytes[b] =
                        static_cast<uint8_t>(byte_dist(rng));
                    page[slot_right].bytes[b] =
                        static_cast<uint8_t>(byte_dist(rng));
                }
                page[slot_left].bytes[0] |= 0x01;
                page[slot_right].bytes[0] |= 0x01;
            }
        }

        return page;
    }

    // Defeat dead-store elimination on the bytes32_t result.
    void sink_bytes32(bytes32_t const &b)
    {
        asm volatile("" : : "r"(b.bytes) : "memory");
    }

    // Local replica of the bitmap-derivation done at the top of page_commit
    // (the production version lives in an anonymous namespace inside
    // storage_page.cpp). Replicated here so we can time it in isolation:
    // the Rust SMC harness takes the bitmap as input and so doesn't pay this
    // cost; measuring it lets us subtract from the C++ total to compare
    // apples-to-apples.
    using slot_bitmap_t = unsigned __int128;

    struct page_bitmaps_local_t
    {
        slot_bitmap_t slot;
        uint64_t pair;
    };

    page_bitmaps_local_t compute_page_bitmaps_local(storage_page_t const &page)
    {
        auto const slot_or = [](uint8_t const *const p) {
            uint64_t limbs[4];
            std::memcpy(limbs, p, sizeof(limbs));
            return limbs[0] | limbs[1] | limbs[2] | limbs[3];
        };

        page_bitmaps_local_t out{0, 0};
        slot_bitmap_t slot_mask = 1;
        uint64_t pair_mask = 1;
        for (size_t i = 0; i < 64; ++i, pair_mask <<= 1) {
            uint64_t const lo = slot_or(page.slots[i * 2].bytes);
            uint64_t const hi = slot_or(page.slots[i * 2 + 1].bytes);
            if (lo != 0) {
                out.slot |= slot_mask;
            }
            slot_mask <<= 1;
            if (hi != 0) {
                out.slot |= slot_mask;
            }
            slot_mask <<= 1;
            if ((lo | hi) != 0) {
                out.pair |= pair_mask;
            }
        }
        return out;
    }

    void sink_bitmaps(page_bitmaps_local_t const &b)
    {
        asm volatile(
            ""
            :
            : "r"(static_cast<uint64_t>(b.slot)), "r"(b.pair)
            : "memory");
    }

    void bench_page_commit(size_t const num_words, size_t const iterations)
    {
        // Clone the page across iterations to keep the access pattern realistic
        // (same as the Rust harness, which indexes into a vector of clones).
        size_t const total = iterations + iterations / 10;
        std::vector<storage_page_t> pages(
            total, build_unique_pair_page(num_words, /*seed=*/99));

        size_t idx = 0;
        auto const t = benchmark_with_timing(
            [&] {
                bytes32_t const out = page_commit(pages[idx]);
                sink_bytes32(out);
                ++idx;
            },
            iterations);

        size_t const pairs = std::min<size_t>(num_words, 64);
        std::printf(
            "page_commit,128,%zu,%zu,sparse_%zu,%lu,%.2f\n",
            num_words,
            pairs,
            num_words,
            static_cast<unsigned long>(t.median_cycles),
            static_cast<double>(t.median_nanos) / 1000.0);
    }

    // Times only the work that page_commit does that the Rust SMC API skips:
    // the single-pass derivation of (slot_bitmap, pair_bitmap) from the page
    // bytes. Subtract this from `page_commit` rows for an apples-to-apples
    // comparison vs Rust SMC simple.
    void bench_prep_only(size_t const num_words, size_t const iterations)
    {
        size_t const total = iterations + iterations / 10;
        std::vector<storage_page_t> pages(
            total, build_unique_pair_page(num_words, /*seed=*/99));

        size_t idx = 0;
        auto const t = benchmark_with_timing(
            [&] {
                auto const b = compute_page_bitmaps_local(pages[idx]);
                sink_bitmaps(b);
                ++idx;
            },
            iterations);

        size_t const pairs = std::min<size_t>(num_words, 64);
        std::printf(
            "prep_only,128,%zu,%zu,sparse_%zu,%lu,%.2f\n",
            num_words,
            pairs,
            num_words,
            static_cast<unsigned long>(t.median_cycles),
            static_cast<double>(t.median_nanos) / 1000.0);
    }
} // namespace

int main()
{
    constexpr size_t ITERATIONS = 5000;

    std::printf("strategy,page_words,words,pairs,workload,cycles,latency_us\n");

    constexpr size_t pair_counts[] = {
        1, 2, 4, 8, 16, 32, 40, 48, 56, 57, 58, 59, 60, 61, 62, 63, 64, 128};
    for (size_t const nw : pair_counts) {
        bench_page_commit(nw, ITERATIONS);
        bench_prep_only(nw, ITERATIONS);
    }

    return 0;
}
