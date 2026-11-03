// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/blocked_bloom_filter.hpp>

#include <gtest/gtest.h>

#include <bit>
#include <cstdint>
#include <cstring>
#include <span>
#include <thread>
#include <vector>

using namespace monad;

namespace
{
    // splitmix64: distinct, well-mixed hashes for key i
    uint64_t mix(uint64_t x)
    {
        x += 0x9e3779b97f4a7c15ULL;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
        return x ^ (x >> 31);
    }

    uint64_t h1(uint64_t const key)
    {
        return mix(2 * key);
    }

    uint64_t h2(uint64_t const key)
    {
        return mix(2 * key + 1);
    }
}

TEST(BlockedBloomFilter, no_false_negatives)
{
    BlockedBloomFilter filter{BlockedBloomFilter::blocks_for_size(1 << 20), 6};
    for (uint64_t key = 0; key < 200'000; ++key) {
        filter.insert(h1(key), h2(key));
    }
    for (uint64_t key = 0; key < 200'000; ++key) {
        ASSERT_TRUE(filter.may_contain(h1(key), h2(key))) << key;
    }
}

TEST(BlockedBloomFilter, false_positive_rate)
{
    constexpr uint64_t KEYS = 200'000;
    for (double const bits_per_key : {10.0, 16.0, 24.0}) {
        BlockedBloomFilter filter{
            BlockedBloomFilter::blocks_for_size(
                static_cast<size_t>(KEYS * bits_per_key / 8)),
            BlockedBloomFilter::optimal_num_probes(bits_per_key)};
        for (uint64_t key = 0; key < KEYS; ++key) {
            filter.insert(h1(key), h2(key));
        }
        constexpr uint64_t QUERIES = 2'000'000;
        uint64_t positives = 0;
        for (uint64_t key = KEYS; key < KEYS + QUERIES; ++key) {
            positives += filter.may_contain(h1(key), h2(key)) ? 1 : 0;
        }
        double const measured =
            static_cast<double>(positives) / static_cast<double>(QUERIES);
        double const estimated = filter.false_positive_rate();
        // A standard bloom filter's rate at these sizes is 0.82%, 0.046% and
        // 0.0012%; blocking costs a small factor
        double const bound = bits_per_key == 10.0   ? 0.015
                             : bits_per_key == 16.0 ? 0.0015
                                                    : 0.0002;
        EXPECT_LT(measured, bound) << bits_per_key << " bits per key";
        EXPECT_GT(estimated, measured / 3) << bits_per_key << " bits per key";
        EXPECT_LT(estimated, measured * 3 + 1e-5)
            << bits_per_key << " bits per key";
    }
}

TEST(BlockedBloomFilter, concurrent_inserts_and_queries)
{
    BlockedBloomFilter filter{BlockedBloomFilter::blocks_for_size(1 << 20), 6};
    constexpr uint64_t PER_THREAD = 50'000;
    constexpr unsigned THREADS = 4;
    std::vector<std::thread> threads;
    for (unsigned t = 0; t < THREADS; ++t) {
        threads.emplace_back([&filter, t] {
            for (uint64_t i = 0; i < PER_THREAD; ++i) {
                uint64_t const key = t * PER_THREAD + i;
                filter.insert(h1(key), h2(key));
                // a key is visible to its inserting thread at once
                EXPECT_TRUE(filter.may_contain(h1(key), h2(key)));
            }
        });
    }
    for (auto &thread : threads) {
        thread.join();
    }
    for (uint64_t key = 0; key < THREADS * PER_THREAD; ++key) {
        ASSERT_TRUE(filter.may_contain(h1(key), h2(key))) << key;
    }
}

TEST(BlockedBloomFilter, copy_words_restores_the_same_filter)
{
    BlockedBloomFilter a{BlockedBloomFilter::blocks_for_size(64 << 10), 7};
    for (uint64_t key = 0; key < 20'000; ++key) {
        a.insert(h1(key), h2(key));
    }
    std::vector<uint64_t> words(a.num_words());
    a.copy_words(0, std::span{words}.first(100));
    a.copy_words(100, std::span{words}.subspan(100));

    BlockedBloomFilter b{a.num_blocks(), a.num_probes()};
    ASSERT_EQ(b.bytes().size(), words.size() * sizeof(uint64_t));
    std::memcpy(b.bytes().data(), words.data(), b.bytes().size());
    for (uint64_t key = 0; key < 100'000; ++key) {
        ASSERT_EQ(
            a.may_contain(h1(key), h2(key)), b.may_contain(h1(key), h2(key)))
            << key;
    }
    EXPECT_EQ(a.fill_ratio(), b.fill_ratio());
}

TEST(BlockedBloomFilter, sizes_and_probes)
{
    EXPECT_EQ(BlockedBloomFilter::blocks_for_size(0), 1);
    EXPECT_EQ(BlockedBloomFilter::blocks_for_size(64), 1);
    EXPECT_EQ(BlockedBloomFilter::blocks_for_size(130), 2);
    EXPECT_EQ(BlockedBloomFilter::blocks_for_size(size_t{1} << 30), 1u << 24);

    EXPECT_EQ(BlockedBloomFilter::optimal_num_probes(0.5), 1);
    EXPECT_EQ(BlockedBloomFilter::optimal_num_probes(10), 7);
    EXPECT_EQ(
        BlockedBloomFilter::optimal_num_probes(100),
        BlockedBloomFilter::MAX_PROBES);

    BlockedBloomFilter const filter{3, 4};
    EXPECT_EQ(filter.size_bytes(), 3 * BlockedBloomFilter::BLOCK_BYTES);
    EXPECT_EQ(filter.num_words(), 24);
    EXPECT_EQ(filter.fill_ratio(), 0);
    EXPECT_EQ(filter.false_positive_rate(), 0);
}

TEST(BlockedBloomFilter, one_key_sets_at_most_num_probes_bits_in_one_block)
{
    BlockedBloomFilter filter{1024, 8};
    filter.insert(h1(42), h2(42));
    std::vector<uint64_t> words(filter.num_words());
    filter.copy_words(0, words);
    unsigned bits = 0;
    unsigned blocks = 0;
    for (size_t b = 0; b < filter.num_blocks(); ++b) {
        unsigned in_block = 0;
        for (size_t w = 0; w < 8; ++w) {
            in_block += static_cast<unsigned>(std::popcount(words[b * 8 + w]));
        }
        bits += in_block;
        blocks += in_block > 0 ? 1 : 0;
    }
    EXPECT_EQ(blocks, 1);
    EXPECT_GE(bits, 1);
    EXPECT_LE(bits, 8);
}
