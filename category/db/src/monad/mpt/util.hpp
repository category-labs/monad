#pragma once

#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/hex_literal.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>

#include <concepts>

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
static constexpr uint64_t MIN_HISTORY_LENGTH = 257;

static byte_string const empty_trie_hash = [] {
    using namespace ::monad::literals;
    return 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_hex;
}();

struct virtual_chunk_offset_t
{
    file_offset_t offset : 28; //!< Offset into the chunk, max is 256Mb
    file_offset_t
        count : 20; //!< Count of the chunk, max is 1 million, therefore maximum
                    //!< addressable storage is 256Tb
    file_offset_t spare : 15;
    file_offset_t is_in_fast_list : 1;

    static constexpr file_offset_t max_offset = (1ULL << 28) - 1;
    static constexpr file_offset_t max_count = (1U << 20) - 1;
    static constexpr file_offset_t max_spare = (1U << 15) - 1;

    static constexpr virtual_chunk_offset_t invalid_value() noexcept
    {
        return {max_count, max_offset, 1, max_spare};
    }

    constexpr virtual_chunk_offset_t(
        uint32_t count_, file_offset_t offset_, file_offset_t is_fast_list_,
        file_offset_t spare_ = max_spare)
        : offset(offset_ & max_offset)
        , count(count_ & max_count)
        , spare{spare_ & max_spare}
        , is_in_fast_list(is_fast_list_ & 1)
    {
        MONAD_DEBUG_ASSERT(spare_ <= max_spare);
        MONAD_DEBUG_ASSERT(count_ <= max_count);
        MONAD_DEBUG_ASSERT(offset_ <= max_offset);
        MONAD_DEBUG_ASSERT(is_fast_list_ <= 1);
    }

    // note that comparator ignores `spare` and `is_in_fast_list`
    constexpr bool operator==(virtual_chunk_offset_t const &o) const noexcept
    {
        return count == o.count && offset == o.offset;
    }

    constexpr auto operator<=>(virtual_chunk_offset_t const &o) const noexcept
    {
        if (count == o.count && offset == o.offset) {
            return std::weak_ordering::equivalent;
        }
        if (count < o.count || (count == o.count && offset < o.offset)) {
            return std::weak_ordering::less;
        }
        return std::weak_ordering::greater;
    }

    constexpr bool in_fast_list() const noexcept
    {
        return is_in_fast_list;
    }

    constexpr file_offset_t raw() const noexcept
    {
        union _
        {
            file_offset_t ret;
            virtual_chunk_offset_t self;

            constexpr _()
                : ret{}
            {
            }
        } u;

        u.self = *this;
        u.self.spare =
            0; // must be flattened, otherwise can't go into the rbtree key
        u.self.is_in_fast_list = 0;
        return u.ret;
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
    constexpr size_t operator()(virtual_chunk_offset_t v) const noexcept
    {
        return fnv1a_hash<file_offset_t>()(v.raw());
    }
};

//! Low resolution offset type that truncates the last 16 bits of
//! virtual_chunk_offset_t, for which we save space for `Node` without
//! losing too much granularity in compaction offset.
class compact_virtual_chunk_offset_t
{
    static constexpr unsigned most_significant_bits = sizeof(uint32_t) * 8;
    static constexpr unsigned bits_to_truncate = 48 - most_significant_bits;
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
        prevent_public_construction_tag, uint32_t v)
        : v_{v}
    {
    }

    constexpr compact_virtual_chunk_offset_t(
        virtual_chunk_offset_t const offset)
        : v_{static_cast<uint32_t>(offset.raw() >> bits_to_truncate)}
    {
        MONAD_DEBUG_ASSERT(offset != INVALID_VIRTUAL_OFFSET);
    }

    void set_value(uint32_t v) noexcept
    {
        v_ = v;
    }

    constexpr uint32_t get_count() const
    {
        // most significant 20 bits
        static constexpr unsigned count_bits = 20;
        return v_ >> (most_significant_bits - count_bits);
    }

    constexpr operator uint32_t() const noexcept
    {
        return v_;
    }

    constexpr bool
    operator==(compact_virtual_chunk_offset_t const &o) const noexcept
    {
        return v_ == o.v_;
    }

    constexpr auto
    operator<=>(compact_virtual_chunk_offset_t const &o) const noexcept
    {
        return v_ <=> o.v_;
    }

    constexpr compact_virtual_chunk_offset_t
    operator-(compact_virtual_chunk_offset_t const &o) const noexcept
    {
        return {prevent_public_construction_tag{}, v_ - o.v_};
    }

    constexpr compact_virtual_chunk_offset_t &
    operator+=(compact_virtual_chunk_offset_t const &o)
    {
        v_ += o.v_;
        return *this;
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

inline constexpr unsigned
bitmask_index(uint16_t const mask, unsigned const i) noexcept
{
    MONAD_DEBUG_ASSERT(i < 16);
    uint16_t const filter = UINT16_MAX >> (16 - i);
    return static_cast<unsigned>(
        std::popcount(static_cast<uint16_t>(mask & filter)));
}

//! convert an integral's least significant N bytes to a size-N byte string
template <int N, std::unsigned_integral UnsignedInteger>
inline byte_string serialize_as_big_endian(UnsignedInteger n)
{
    MONAD_ASSERT(N <= sizeof(UnsignedInteger));

    // std::byteswap is C++23 only, using GCC intrinsic instead
    if constexpr (std::endian::native != std::endian::big) {
        if constexpr (sizeof(UnsignedInteger) <= 2) {
            n = __builtin_bswap16(n);
        }
        else if constexpr (sizeof(UnsignedInteger) == 4) {
            n = __builtin_bswap32(n);
        }
        else if constexpr (sizeof(UnsignedInteger) == 8) {
            n = __builtin_bswap64(n);
        }
        else {
            return serialize_as_big_endian<N>(static_cast<uint64_t>(n));
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
    UnsignedInteger bit =
        static_cast<UnsignedInteger>(1UL << ((in.nibble_size() - 1) * 4));
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

MONAD_MPT_NAMESPACE_END
