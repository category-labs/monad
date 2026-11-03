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

#include <category/core/assert.h>
#include <category/core/blocked_bloom_filter.hpp>
#include <category/core/config.hpp>

#include <sys/mman.h>

#include <algorithm>
#include <atomic>
#include <bit>
#include <cerrno>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr size_t WORDS_PER_BLOCK = 8;

// The bits a key sets in each 64-bit word of its block. Probe i takes the top
// 9 bits of h2 after i multiplicative rehashes.
struct BlockMask
{
    uint64_t word[WORDS_PER_BLOCK]{};
};

BlockMask block_mask(uint64_t h2, unsigned const num_probes) noexcept
{
    BlockMask mask;
    for (unsigned i = 0; i < num_probes; ++i) {
        unsigned const bit = static_cast<unsigned>(h2 >> 55);
        mask.word[bit >> 6] |= uint64_t{1} << (bit & 63);
        h2 *= 0x9e3779b97f4a7c15ULL;
    }
    return mask;
}

// Maps h1 uniformly onto [0, num_blocks) without a division (Lemire).
uint64_t block_index(uint64_t const h1, uint64_t const num_blocks) noexcept
{
    return static_cast<uint64_t>(
        (static_cast<unsigned __int128>(h1) * num_blocks) >> 64);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

static_assert(BlockedBloomFilter::BLOCK_BYTES == WORDS_PER_BLOCK * 8);

BlockedBloomFilter::BlockedBloomFilter(
    uint64_t const num_blocks, unsigned const num_probes)
    : num_blocks_{num_blocks}
    , num_probes_{num_probes}
{
    MONAD_ASSERT(num_blocks_ > 0);
    MONAD_ASSERT(num_probes_ >= 1 && num_probes_ <= MAX_PROBES);
    void *const data = mmap(
        nullptr,
        size_bytes(),
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS,
        -1,
        0);
    MONAD_ASSERT_PRINTF(
        data != MAP_FAILED,
        "cannot map %zu bytes for a bloom filter: %s",
        size_bytes(),
        std::strerror(errno));
    // Best effort: fewer TLB misses on random block accesses
    (void)madvise(data, size_bytes(), MADV_HUGEPAGE);
    words_ = static_cast<uint64_t *>(data);
}

BlockedBloomFilter::~BlockedBloomFilter()
{
    if (words_ != nullptr) {
        (void)munmap(words_, size_bytes());
    }
}

void BlockedBloomFilter::insert(uint64_t const h1, uint64_t const h2) noexcept
{
    uint64_t *const block =
        words_ + block_index(h1, num_blocks_) * WORDS_PER_BLOCK;
    BlockMask const mask = block_mask(h2, num_probes_);
    for (size_t i = 0; i < WORDS_PER_BLOCK; ++i) {
        if (mask.word[i] != 0) {
            std::atomic_ref<uint64_t>{block[i]}.fetch_or(
                mask.word[i], std::memory_order_relaxed);
        }
    }
}

bool BlockedBloomFilter::may_contain(
    uint64_t const h1, uint64_t const h2) const noexcept
{
    uint64_t *const block =
        words_ + block_index(h1, num_blocks_) * WORDS_PER_BLOCK;
    BlockMask const mask = block_mask(h2, num_probes_);
    for (size_t i = 0; i < WORDS_PER_BLOCK; ++i) {
        if (mask.word[i] != 0 && (std::atomic_ref<uint64_t>{block[i]}.load(
                                      std::memory_order_relaxed) &
                                  mask.word[i]) != mask.word[i]) {
            return false;
        }
    }
    return true;
}

double BlockedBloomFilter::fill_ratio() const noexcept
{
    uint64_t set = 0;
    uint64_t const num_words = num_blocks_ * WORDS_PER_BLOCK;
    for (uint64_t i = 0; i < num_words; ++i) {
        set += static_cast<uint64_t>(
            std::popcount(std::atomic_ref<uint64_t>{words_[i]}.load(
                std::memory_order_relaxed)));
    }
    return static_cast<double>(set) /
           static_cast<double>(num_words * sizeof(uint64_t) * 8);
}

double BlockedBloomFilter::false_positive_rate() const noexcept
{
    // A random key lands in a uniformly random block, and each of its probes
    // hits a set bit with probability (bits set in that block) / 512. Probes
    // can repeat a bit, which this ignores; the error is small.
    double sum = 0;
    for (uint64_t b = 0; b < num_blocks_; ++b) {
        unsigned set = 0;
        for (size_t i = 0; i < WORDS_PER_BLOCK; ++i) {
            set += static_cast<unsigned>(std::popcount(
                std::atomic_ref<uint64_t>{words_[b * WORDS_PER_BLOCK + i]}.load(
                    std::memory_order_relaxed)));
        }
        sum += std::pow(
            static_cast<double>(set) / static_cast<double>(BLOCK_BITS),
            static_cast<double>(num_probes_));
    }
    return sum / static_cast<double>(num_blocks_);
}

void BlockedBloomFilter::copy_words(
    uint64_t const first_word, std::span<uint64_t> const out) const noexcept
{
    MONAD_ASSERT(first_word + out.size() <= num_words());
    for (size_t i = 0; i < out.size(); ++i) {
        out[i] = std::atomic_ref<uint64_t>{words_[first_word + i]}.load(
            std::memory_order_relaxed);
    }
}

std::span<unsigned char> BlockedBloomFilter::bytes() noexcept
{
    return {reinterpret_cast<unsigned char *>(words_), size_bytes()};
}

uint64_t BlockedBloomFilter::blocks_for_size(size_t const size_bytes) noexcept
{
    return std::max<uint64_t>(1, size_bytes / BLOCK_BYTES);
}

unsigned
BlockedBloomFilter::optimal_num_probes(double const bits_per_key) noexcept
{
    // ln 2 * bits per key, as for a standard Bloom filter. Confining the
    // probes to one block makes block loads vary, which favors slightly fewer
    // probes; the difference in the resulting rate is small.
    double const k = std::round(bits_per_key * 0.6931471805599453);
    return static_cast<unsigned>(
        std::clamp(k, 1.0, static_cast<double>(MAX_PROBES)));
}

MONAD_NAMESPACE_END
