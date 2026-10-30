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

#pragma once

#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <compare>
#include <concepts>
#include <cstdint>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

using chunk_offset_t = MONAD_ASYNC_NAMESPACE::chunk_offset_t;
using chunk_offset_t_hasher = MONAD_ASYNC_NAMESPACE::chunk_offset_t_hasher;
using file_offset_t = MONAD_ASYNC_NAMESPACE::file_offset_t;

using MONAD_ASYNC_NAMESPACE::CPU_PAGE_BITS;
using MONAD_ASYNC_NAMESPACE::CPU_PAGE_SIZE;
using MONAD_ASYNC_NAMESPACE::DISK_PAGE_BITS;
using MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE;
using MONAD_ASYNC_NAMESPACE::DMA_PAGE_BITS;
using MONAD_ASYNC_NAMESPACE::DMA_PAGE_SIZE;
using MONAD_ASYNC_NAMESPACE::INVALID_OFFSET;

using MONAD_ASYNC_NAMESPACE::round_down_align;
using MONAD_ASYNC_NAMESPACE::round_up_align;

static constexpr uint8_t INVALID_BRANCH = 255;
static constexpr uint8_t INVALID_PATH_INDEX = 255;
static constexpr uint64_t INVALID_BLOCK_NUM = uint64_t(-1);
// Floor for disk-pressure history shrinking. Execution requires 256 history
// blocks for the block hash buffer, so this must exceed 256 by enough margin
// that a node rewound to the last finalized block on restart still has
// sufficient history and can avoid a full statesync.
static constexpr uint64_t MIN_HISTORY_LENGTH = 300;

static byte_string const empty_trie_hash = [] {
    using namespace ::monad::literals;
    return 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes;
}();

struct virtual_chunk_offset_t
{
    static constexpr unsigned OFFSET_BITS = chunk_offset_t::OFFSET_BITS;
    static constexpr unsigned COUNT_BITS = chunk_offset_t::ID_BITS;
    static constexpr unsigned SPARE_BITS = chunk_offset_t::SPARE_BITS;

    file_offset_t offset : OFFSET_BITS; //!< Offset into the chunk, max is 256Mb
    file_offset_t count : COUNT_BITS; //!< Count of the chunk, max is 1 million,
                                      //!< therefore maximum addressable storage
                                      //!< is 256Tb
    file_offset_t spare : SPARE_BITS;
    file_offset_t is_in_fast_list : 1;

    static constexpr file_offset_t MAX_OFFSET = (1ULL << OFFSET_BITS) - 1;
    static constexpr file_offset_t MAX_COUNT = (1U << COUNT_BITS) - 1;
    static constexpr file_offset_t MAX_SPARE = (1U << SPARE_BITS) - 1;

    static constexpr virtual_chunk_offset_t invalid_value() noexcept
    {
        return {MAX_COUNT, MAX_OFFSET, 1, MAX_SPARE};
    }

    constexpr virtual_chunk_offset_t(
        uint32_t const count_, file_offset_t const offset_,
        file_offset_t const is_fast_list_,
        file_offset_t const spare_ = MAX_SPARE)
        : offset(offset_ & MAX_OFFSET)
        , count(count_ & MAX_COUNT)
        , spare{spare_ & MAX_SPARE}
        , is_in_fast_list(is_fast_list_ & 1)
    {
        MONAD_ASSERT(spare_ <= MAX_SPARE);
        MONAD_ASSERT(count_ <= MAX_COUNT);
        MONAD_ASSERT(offset_ <= MAX_OFFSET);
        MONAD_ASSERT(is_fast_list_ <= 1);
    }

    // note that comparator ignores `spare`
    constexpr bool operator==(virtual_chunk_offset_t const &o) const noexcept
    {
        return is_in_fast_list == o.is_in_fast_list && count == o.count &&
               offset == o.offset;
    }

    constexpr bool in_fast_list() const noexcept
    {
        return is_in_fast_list;
    }

    // ignore `spare` and `is_in_fast_list`
    constexpr file_offset_t raw() const noexcept
    {
        return (static_cast<file_offset_t>(count) << OFFSET_BITS) |
               static_cast<file_offset_t>(offset);
    }

    // for hash table key, only ignore `spare`
    constexpr file_offset_t hasher_raw() const noexcept
    {
        return (static_cast<file_offset_t>(is_in_fast_list)
                << (OFFSET_BITS + COUNT_BITS + SPARE_BITS)) |
               (static_cast<file_offset_t>(count) << OFFSET_BITS) |
               static_cast<file_offset_t>(offset);
    }
};

static_assert(sizeof(virtual_chunk_offset_t) == 8);
static_assert(alignof(virtual_chunk_offset_t) == 8);
static_assert(std::is_trivially_copyable_v<virtual_chunk_offset_t>);

//! The invalid virtual file offset
static constexpr virtual_chunk_offset_t INVALID_VIRTUAL_OFFSET =
    virtual_chunk_offset_t::invalid_value();
static_assert(INVALID_VIRTUAL_OFFSET.in_fast_list());

struct virtual_chunk_offset_t_hasher
{
    constexpr size_t operator()(virtual_chunk_offset_t const v) const noexcept
    {
        return fnv1a_hash<file_offset_t>()(v.hasher_raw());
    }
};

//! Low resolution offset type that truncates the last 16 bits of
//! virtual_chunk_offset_t, for which we save space for `Node` without
//! losing too much granularity in compaction offset.
class compact_virtual_chunk_offset_t
{
    static constexpr unsigned most_significant_bits = sizeof(uint32_t) * 8;

public:
    static constexpr unsigned bits_to_truncate =
        virtual_chunk_offset_t::OFFSET_BITS +
        virtual_chunk_offset_t::COUNT_BITS - most_significant_bits;
    //! Width of what is left of the chunk offset, below the count.
    static constexpr unsigned TRUNCATED_OFFSET_BITS =
        most_significant_bits - virtual_chunk_offset_t::COUNT_BITS;

private:
    uint32_t v_{0};

    struct prevent_public_construction_tag
    {
    };

public:
    static constexpr compact_virtual_chunk_offset_t invalid_value() noexcept
    {
        return {prevent_public_construction_tag{}, uint32_t(-1)};
    }

    static constexpr compact_virtual_chunk_offset_t min_value() noexcept
    {
        return {prevent_public_construction_tag{}, 0};
    }

    constexpr compact_virtual_chunk_offset_t(
        prevent_public_construction_tag, uint32_t const v)
        : v_{v}
    {
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr compact_virtual_chunk_offset_t(
        virtual_chunk_offset_t const offset)
        : v_{static_cast<uint32_t>(offset.raw() >> bits_to_truncate)}
    {
        MONAD_ASSERT(offset != INVALID_VIRTUAL_OFFSET);
    }

    void set_value(uint32_t const v) noexcept
    {
        v_ = v;
    }

    constexpr uint32_t get_count() const
    {
        return v_ >>
               (most_significant_bits - virtual_chunk_offset_t::COUNT_BITS);
    }

    constexpr uint32_t get_truncated_offset() const noexcept
    {
        return v_ & ((1u << TRUNCATED_OFFSET_BITS) - 1);
    }

    static constexpr compact_virtual_chunk_offset_t
    from_count_and_truncated_offset(
        uint32_t const count, uint32_t const truncated_offset) noexcept
    {
        MONAD_ASSERT(count < virtual_chunk_offset_t::MAX_COUNT);
        MONAD_ASSERT((truncated_offset >> TRUNCATED_OFFSET_BITS) == 0);
        return {
            prevent_public_construction_tag{},
            (count << TRUNCATED_OFFSET_BITS) | truncated_offset};
    }

    constexpr explicit operator uint32_t() const noexcept
    {
        return v_;
    }

    constexpr bool
    operator==(compact_virtual_chunk_offset_t const &o) const noexcept
    {
        return v_ == o.v_;
    }
};

static_assert(sizeof(compact_virtual_chunk_offset_t) == 4);
static_assert(alignof(compact_virtual_chunk_offset_t) == 4);
static_assert(std::is_trivially_copyable_v<compact_virtual_chunk_offset_t>);

//! The invalid and min compact_virtual_chunk_offset_t
static constexpr compact_virtual_chunk_offset_t INVALID_COMPACT_VIRTUAL_OFFSET =
    compact_virtual_chunk_offset_t::invalid_value();

static constexpr compact_virtual_chunk_offset_t MIN_COMPACT_VIRTUAL_OFFSET =
    compact_virtual_chunk_offset_t::min_value();

//! A pair of compact virtual chunk offsets for fast and slow lists.
struct compact_offset_pair
{
    compact_virtual_chunk_offset_t fast{INVALID_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t slow{INVALID_COMPACT_VIRTUAL_OFFSET};

    byte_string serialize() const;

    static compact_offset_pair deserialize(byte_string_view bytes);

    constexpr bool
    operator==(compact_offset_pair const &) const noexcept = default;
};

static_assert(sizeof(compact_offset_pair) == 8);
static_assert(alignof(compact_offset_pair) == 4);

//! Fast and slow insertion counts run 0, 1, ..., INSERTION_COUNT_PERIOD, 1,
//! ...: 0 names only the first chunk of an empty list and MAX_COUNT is never
//! assigned. So no live offset compacts to INVALID_COMPACT_VIRTUAL_OFFSET,
//! and only offsets in the first 64 KiB of a count-0 chunk compact to
//! MIN_COMPACT_VIRTUAL_OFFSET, which they sort equal to.
inline constexpr uint32_t INSERTION_COUNT_PERIOD =
    virtual_chunk_offset_t::MAX_COUNT - 1;

constexpr uint32_t next_insertion_count(uint32_t const count) noexcept
{
    MONAD_ASSERT(count <= INSERTION_COUNT_PERIOD);
    return count == INSERTION_COUNT_PERIOD ? 1 : count + 1;
}

//! Distance between two compact offsets of one chunk list, in units of
//! 1 << compact_virtual_chunk_offset_t::bits_to_truncate bytes.
enum class compact_distance : uint32_t
{
};

constexpr uint32_t units(compact_distance const d) noexcept
{
    return std::to_underlying(d);
}

constexpr uint64_t bytes(compact_distance const d) noexcept
{
    return uint64_t{units(d)}
           << compact_virtual_chunk_offset_t::bits_to_truncate;
}

//! Orders one chunk list's offsets by their distance from the list's head
//! chunk, which stays correct once the list's insertion counts wrap. Only
//! offsets at or after the head compare meaningfully, and the order is stale
//! once a chunk is released from the head.
class chunk_list_order
{
    uint32_t head_count_;

    static constexpr uint32_t residue_(uint32_t const count) noexcept
    {
        return count % INSERTION_COUNT_PERIOD;
    }

    constexpr uint32_t count_at_rank_(uint32_t const chunk_rank) const noexcept
    {
        if (chunk_rank == 0) {
            return head_count_;
        }
        uint32_t const r =
            (residue_(head_count_) + chunk_rank) % INSERTION_COUNT_PERIOD;
        return r == 0 ? INSERTION_COUNT_PERIOD : r;
    }

public:
    explicit constexpr chunk_list_order(uint32_t const head_count) noexcept
        : head_count_{head_count}
    {
        MONAD_ASSERT(head_count <= INSERTION_COUNT_PERIOD);
    }

    constexpr uint32_t head_count() const noexcept
    {
        return head_count_;
    }

    //! Chunks between the head and the chunk with insertion count `count`.
    constexpr uint32_t rank(uint32_t const count) const noexcept
    {
        MONAD_ASSERT(count <= INSERTION_COUNT_PERIOD);
        return (residue_(count) + INSERTION_COUNT_PERIOD -
                residue_(head_count_)) %
               INSERTION_COUNT_PERIOD;
    }

    //! MIN sorts at or below, and INVALID above, every live offset.
    constexpr uint32_t
    key(compact_virtual_chunk_offset_t const x) const noexcept
    {
        if (x == INVALID_COMPACT_VIRTUAL_OFFSET) {
            return UINT32_MAX;
        }
        if (x == MIN_COMPACT_VIRTUAL_OFFSET) {
            return 0;
        }
        return (rank(x.get_count())
                << compact_virtual_chunk_offset_t::TRUNCATED_OFFSET_BITS) |
               x.get_truncated_offset();
    }

    constexpr bool less(
        compact_virtual_chunk_offset_t const a,
        compact_virtual_chunk_offset_t const b) const noexcept
    {
        return key(a) < key(b);
    }

    constexpr compact_virtual_chunk_offset_t
    min(compact_virtual_chunk_offset_t const a,
        compact_virtual_chunk_offset_t const b) const noexcept
    {
        return less(b, a) ? b : a;
    }

    //! Whole chunks before `x`'s chunk: what a GC boundary at `x` frees.
    constexpr uint32_t
    chunks_before(compact_virtual_chunk_offset_t const x) const noexcept
    {
        MONAD_ASSERT(x != INVALID_COMPACT_VIRTUAL_OFFSET);
        return key(x) >> compact_virtual_chunk_offset_t::TRUNCATED_OFFSET_BITS;
    }

    //! Whether `x` is in the list's first `chunks` chunks.
    constexpr bool contains(
        compact_virtual_chunk_offset_t const x,
        uint32_t const chunks) const noexcept
    {
        MONAD_ASSERT(x != INVALID_COMPACT_VIRTUAL_OFFSET);
        // rank() aliases count 0 with INSERTION_COUNT_PERIOD, and count 0
        // only ever names a list's first chunk.
        if (x.get_count() == 0) {
            return head_count_ == 0;
        }
        return rank(x.get_count()) < chunks;
    }

    constexpr compact_distance distance(
        compact_virtual_chunk_offset_t const from,
        compact_virtual_chunk_offset_t const to) const noexcept
    {
        MONAD_ASSERT(
            from != INVALID_COMPACT_VIRTUAL_OFFSET &&
            to != INVALID_COMPACT_VIRTUAL_OFFSET);
        return compact_distance{key(to) - key(from)};
    }

    constexpr compact_virtual_chunk_offset_t advance(
        compact_virtual_chunk_offset_t const from,
        compact_distance const d) const noexcept
    {
        MONAD_ASSERT(from != INVALID_COMPACT_VIRTUAL_OFFSET);
        constexpr unsigned bits =
            compact_virtual_chunk_offset_t::TRUNCATED_OFFSET_BITS;
        uint64_t const k = uint64_t{key(from)} + units(d);
        uint64_t const chunk_rank = k >> bits;
        MONAD_ASSERT(chunk_rank < INSERTION_COUNT_PERIOD);
        return compact_virtual_chunk_offset_t::from_count_and_truncated_offset(
            count_at_rank_(static_cast<uint32_t>(chunk_rank)),
            static_cast<uint32_t>(k) & ((1u << bits) - 1));
    }
};

//! The fast and slow lists' orders, as they stood when taken.
struct offset_order
{
    chunk_list_order fast;
    chunk_list_order slow;

    constexpr chunk_list_order const &
    list(bool const in_fast_list) const noexcept
    {
        return in_fast_list ? fast : slow;
    }

    constexpr bool any_below(
        compact_offset_pair const x,
        compact_offset_pair const threshold) const noexcept
    {
        return fast.less(x.fast, threshold.fast) ||
               slow.less(x.slow, threshold.slow);
    }

    constexpr bool fast_below(
        compact_offset_pair const x,
        compact_offset_pair const threshold) const noexcept
    {
        return fast.less(x.fast, threshold.fast);
    }

    //! Whether `x` is below the component of `threshold` for its own list.
    constexpr bool below(
        virtual_chunk_offset_t const x,
        compact_offset_pair const threshold) const noexcept
    {
        MONAD_ASSERT(x != INVALID_VIRTUAL_OFFSET);
        bool const in_fast = x.in_fast_list();
        return list(in_fast).less(
            compact_virtual_chunk_offset_t{x},
            in_fast ? threshold.fast : threshold.slow);
    }

    constexpr compact_offset_pair
    min(compact_offset_pair const a, compact_offset_pair const b) const noexcept
    {
        return {fast.min(a.fast, b.fast), slow.min(a.slow, b.slow)};
    }

    //! Slow-list offsets order before fast-list ones.
    constexpr std::strong_ordering compare(
        virtual_chunk_offset_t const a,
        virtual_chunk_offset_t const b) const noexcept
    {
        MONAD_ASSERT(
            a != INVALID_VIRTUAL_OFFSET && b != INVALID_VIRTUAL_OFFSET);
        if (a.in_fast_list() != b.in_fast_list()) {
            return a.in_fast_list() <=> b.in_fast_list();
        }
        auto const &l = list(a.in_fast_list());
        uint32_t const rank_a = l.rank(static_cast<uint32_t>(a.count));
        uint32_t const rank_b = l.rank(static_cast<uint32_t>(b.count));
        if (rank_a != rank_b) {
            return rank_a <=> rank_b;
        }
        return static_cast<file_offset_t>(a.offset) <=>
               static_cast<file_offset_t>(b.offset);
    }
};

//! Insertion counts of one chunk list's head and tail chunks.
struct chunk_list_counts
{
    uint32_t head;
    uint32_t tail;
};

struct fast_slow_list_counts
{
    chunk_list_counts fast;
    chunk_list_counts slow;
};

//! A chunk list's tail chunk id and that chunk's whole metadata word.
struct chunk_list_tail_state
{
    uint32_t id;
    uint64_t chunk_info;

    bool operator==(chunk_list_tail_state const &) const = default;
};

struct fast_slow_tail_states
{
    chunk_list_tail_state fast;
    chunk_list_tail_state slow;

    bool operator==(fast_slow_tail_states const &) const = default;
};

constexpr unsigned bitmask_index(uint16_t const mask, unsigned const i) noexcept
{
    MONAD_ASSERT(i < 16);
    MONAD_ASSERT(mask & (1u << i));
    uint16_t const filter = UINT16_MAX >> (16 - i);
    return static_cast<unsigned>(
        std::popcount(static_cast<uint16_t>(mask & filter)));
}

//! convert an integral's least significant N bytes to a size-N byte string
template <int N, std::unsigned_integral UnsignedInteger>
inline byte_string serialize_as_big_endian(UnsignedInteger n)
{
    MONAD_ASSERT(N <= sizeof(UnsignedInteger));

    if constexpr (std::endian::native != std::endian::big) {
        // Wider than a word: swap and slice the low 8 bytes, which is all N can
        // select given the assert above.
        if constexpr (sizeof(UnsignedInteger) > 8) {
            return serialize_as_big_endian<N>(static_cast<uint64_t>(n));
        }
        else {
            n = bswap(n);
        }
    }
    auto arr =
        std::bit_cast<std::array<unsigned char, sizeof(UnsignedInteger)>>(n);
    return byte_string{arr.data() + sizeof(n) - N, N};
}

template <std::unsigned_integral UnsignedInteger>
inline UnsignedInteger deserialize_from_big_endian(NibblesView const in)
{
    if (in.nibble_size() > sizeof(UnsignedInteger) * 2) {
        throw std::runtime_error(
            "input bytes to deserialize must be less than or "
            "equal to sizeof output type\n");
    }
    UnsignedInteger out = 0;
    UnsignedInteger bit = static_cast<UnsignedInteger>(
        1UL << (std::max((in.nibble_size() - 1), 0) * 4));
    for (auto i = 0; i < in.nibble_size(); ++i, bit >>= 4) {
        out += static_cast<UnsignedInteger>(
            in.get(static_cast<unsigned char>(i)) * bit);
    }
    return out;
}

//! serilaize a value as it is to a byte string
template <std::integral V>
inline byte_string serialize(V n)
{
    static_assert(std::endian::native == std::endian::little);
    auto arr = std::bit_cast<std::array<unsigned char, sizeof(V)>>(n);
    return byte_string{arr.data(), arr.size()};
}

inline byte_string compact_offset_pair::serialize() const
{
    return ::monad::mpt::serialize((uint32_t)fast) +
           ::monad::mpt::serialize((uint32_t)slow);
}

inline compact_offset_pair
compact_offset_pair::deserialize(byte_string_view const bytes)
{
    MONAD_ASSERT(bytes.size() == 2 * sizeof(uint32_t));
    compact_offset_pair offsets;
    // copy size is implicitly part of the `unaligned_load` call
    // NOLINTNEXTLINE(bugprone-suspicious-stringview-data-usage)
    offsets.fast.set_value(unaligned_load<uint32_t>(bytes.data()));
    offsets.slow.set_value(
        unaligned_load<uint32_t>(bytes.data() + sizeof(uint32_t)));
    return offsets;
}

MONAD_MPT_NAMESPACE_END
