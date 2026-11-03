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

#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

// A Bloom filter that keeps all probes of a key inside one 512-bit block, so
// that an insert or a query touches a single cache line instead of one line
// per probe (Putze, Sanders and Singler, "Cache-, Hash- and Space-Efficient
// Bloom Filters"). For the same memory it answers slightly more false
// positives than a standard Bloom filter.
//
// A key is given as two independent, uniformly distributed 64-bit hashes:
// `h1` selects the block and `h2` the bits within it.
//
// Bits are only ever set, with atomic ORs, so inserts and queries may run
// concurrently on any threads. A query answers true for every key whose
// insert happens-before it; there are no false negatives.
class BlockedBloomFilter final
{
    uint64_t *words_{nullptr};
    uint64_t num_blocks_{0};
    unsigned num_probes_{0};

public:
    static constexpr size_t BLOCK_BYTES = 64;
    static constexpr size_t BLOCK_BITS = BLOCK_BYTES * 8;
    static constexpr unsigned MAX_PROBES = 16;

    // Memory is mapped anonymously and zeroed by the kernel on first touch;
    // transparent huge pages are requested for it.
    BlockedBloomFilter(uint64_t num_blocks, unsigned num_probes);
    ~BlockedBloomFilter();

    BlockedBloomFilter(BlockedBloomFilter const &) = delete;
    BlockedBloomFilter &operator=(BlockedBloomFilter const &) = delete;

    void insert(uint64_t h1, uint64_t h2) noexcept;
    bool may_contain(uint64_t h1, uint64_t h2) const noexcept;

    uint64_t num_blocks() const noexcept
    {
        return num_blocks_;
    }

    unsigned num_probes() const noexcept
    {
        return num_probes_;
    }

    size_t size_bytes() const noexcept
    {
        return static_cast<size_t>(num_blocks_) * BLOCK_BYTES;
    }

    // Fraction of the bits that are set. Scans the whole filter.
    double fill_ratio() const noexcept;

    // Probability that a query for a key that was never inserted answers
    // true, given the current contents. Scans the whole filter.
    double false_positive_rate() const noexcept;

    // Copies the filter's 64-bit words starting at `first_word` into `out`,
    // each with an atomic load, so it may run concurrently with inserts: the
    // copy holds every key inserted before the copy started.
    void
    copy_words(uint64_t first_word, std::span<uint64_t> out) const noexcept;

    uint64_t num_words() const noexcept
    {
        return num_blocks_ * (BLOCK_BYTES / sizeof(uint64_t));
    }

    // The filter's bits, for loading. Writes through this span must not run
    // concurrently with inserts or queries.
    std::span<unsigned char> bytes() noexcept;

    // Number of blocks that fit in `size_bytes`, at least one.
    static uint64_t blocks_for_size(size_t size_bytes) noexcept;

    // Number of probes that minimizes the false positive rate at the given
    // number of bits per key, within [1, MAX_PROBES].
    static unsigned optimal_num_probes(double bits_per_key) noexcept;
};

MONAD_NAMESPACE_END
