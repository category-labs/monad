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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/core/nibble.h>
#include <category/mpt/config.hpp>

#include <algorithm>
#include <compare>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>
#include <memory>
#include <span>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

/* A "nibble" here is a trie symbol of NIBBLE_BITS bits (4 for the hexary
Ethereum MPT, 5 for the 32-ary benchmark trie), packed MSB-first into a byte
buffer. A view over a raw byte string of n bytes has nibbles_for_bytes(n)
symbols; when 8n is not a multiple of NIBBLE_BITS the last symbol is padded
with zero bits that are not backed by memory (reads past the buffer return
zero). Owning containers (Nibbles, Node paths) always materialize the padding
byte. */

class NibblesView;
class Node;

constexpr bool operator==(NibblesView const &a, NibblesView const &b);
constexpr std::strong_ordering
operator<=>(NibblesView const &a, NibblesView const &b);

namespace detail
{
    // Read symbol `i` given a bit offset of symbol 0 within data[0]. Reads
    // data[byte + 1] only when it lies within `data_bytes`.
    constexpr unsigned char get_symbol(
        unsigned char const *const data, unsigned const begin_bit,
        unsigned const i, unsigned const data_bytes) noexcept
    {
        if constexpr (NIBBLE_BITS == 4) {
            return ::get_nibble(data, begin_bit / 4 + i);
        }
        else {
            unsigned const bit = begin_bit + i * NIBBLE_BITS;
            unsigned const byte = bit >> 3;
            unsigned const shift = bit & 7;
            unsigned window = static_cast<unsigned>(data[byte]) << 8;
            if (byte + 1 < data_bytes) {
                window |= data[byte + 1];
            }
            return static_cast<unsigned char>(
                (window >> (16 - shift - NIBBLE_BITS)) & MAX_NIBBLE);
        }
    }

    // Write symbol `i`; the buffer must be materialized (bytes_for_bits of
    // begin_bit + (i + 1) * NIBBLE_BITS bytes available).
    constexpr void set_symbol(
        unsigned char *const data, unsigned const begin_bit, unsigned const i,
        unsigned char const value) noexcept
    {
        if constexpr (NIBBLE_BITS == 4) {
            ::set_nibble(data, begin_bit / 4 + i, value);
        }
        else {
            unsigned const bit = begin_bit + i * NIBBLE_BITS;
            unsigned const byte = bit >> 3;
            unsigned const shift = bit & 7;
            unsigned const pos = 16 - shift - NIBBLE_BITS; // from window LSB
            unsigned const mask = static_cast<unsigned>(MAX_NIBBLE) << pos;
            unsigned const val = static_cast<unsigned>(value) << pos;
            unsigned window = static_cast<unsigned>(data[byte]) << 8;
            bool const two = (shift + NIBBLE_BITS) > 8;
            if (two) {
                window |= data[byte + 1];
            }
            window = (window & ~mask) | val;
            data[byte] = static_cast<unsigned char>(window >> 8);
            if (two) {
                data[byte + 1] = static_cast<unsigned char>(window & 0xFF);
            }
        }
    }
}

class Nibbles
{
private:
    friend class NibblesView;
    using size_type = uint8_t; // max length support is 255 nibbles
    std::unique_ptr<unsigned char[]> data_;
    uint8_t begin_bit_{0}; // bit offset of symbol 0 within data_[0]
    size_type nibble_count_{0};

public:
    static constexpr unsigned npos = std::numeric_limits<unsigned>::max();

    constexpr Nibbles() = default;

    Nibbles(Nibbles &&) = default;

    Nibbles &operator=(Nibbles &&) = default;

    explicit Nibbles(size_t const nibble_count)
        : data_(std::make_unique<unsigned char[]>(
              bytes_for_nibbles(static_cast<unsigned>(nibble_count))))
        , begin_bit_(0)
        , nibble_count_(static_cast<size_type>(nibble_count))
    {
        MONAD_ASSERT(nibble_count <= std::numeric_limits<size_type>::max());
#ifdef __clang_analyzer__ // false positive
        memset(
            data_.get(),
            0,
            bytes_for_nibbles(static_cast<unsigned>(nibble_count)));
#endif
    }

    Nibbles(NibblesView other); // NOLINT(google-explicit-constructor)

    Nibbles(Nibbles const &other)
    {
        begin_bit_ = other.begin_bit_;
        nibble_count_ = other.nibble_count_;
        if (nibble_count_ != 0) {
            data_ = std::make_unique<unsigned char[]>(other.data_size());
            std::memcpy(data_.get(), other.data_.get(), other.data_size());
        }
    }

    Nibbles &operator=(Nibbles const &other)
    {
        if (this != &other) {
            begin_bit_ = other.begin_bit_;
            nibble_count_ = other.nibble_count_;
            if (nibble_count_ != 0) {
                data_ = std::make_unique<unsigned char[]>(other.data_size());
                std::memcpy(data_.get(), other.data_.get(), other.data_size());
            }
        }
        return *this;
    }

    unsigned char const *data() const noexcept
    {
        return data_.get();
    }

    // true when symbol 0 does not start on a byte boundary
    bool begin_nibble() const noexcept
    {
        return begin_bit_ != 0;
    }

    [[nodiscard]] bool empty() const noexcept
    {
        return !data_;
    }

    // bytes backing the symbols, including the leading alignment bits and
    // the trailing padding bits
    constexpr unsigned data_size() const noexcept
    {
        return nibble_count_ == 0
                   ? 0
                   : bytes_for_bits(begin_bit_ + nibble_count_ * NIBBLE_BITS);
    }

    constexpr size_type nibble_size() const
    {
        return nibble_count_;
    }

    // Returns a left-aligned Nibbles containing a subrange of nibbles starting
    // at `pos` and up to `count` nibbles (or to the end if count == npos).
    // The returned Nibbles is always left-aligned (begin_bit_ == 0).
    constexpr Nibbles substr(unsigned pos, unsigned count = npos) const;

    [[nodiscard]] unsigned char get(unsigned const i) const
    {
        MONAD_ASSERT(i < nibble_size());
        return detail::get_symbol(data_.get(), begin_bit_, i, data_size());
    }

    constexpr void set(unsigned const i, unsigned char const value)
    {
        MONAD_ASSERT(value <= MAX_NIBBLE);
        MONAD_ASSERT(i < nibble_count_);
        detail::set_symbol(data_.get(), begin_bit_, i, value);
    }
};

static_assert(sizeof(Nibbles) == 16);
static_assert(alignof(Nibbles) == 8);

class NibblesView
{
    friend inline std::ostream &
    operator<<(std::ostream &s, NibblesView const &v);

private:
    friend class Nibbles;
    friend class Node;
    friend class NodeBase;
    using size_type = Nibbles::size_type;
    unsigned char const *data_{nullptr};
    uint8_t begin_bit_{0}; // bit offset of symbol 0 within data_[0]
    size_type nibble_count_{0};
    // bytes readable from data_; may be one short of data_size() for a view
    // over a raw byte string whose last symbol is zero padded
    uint8_t data_bytes_{0};

    constexpr NibblesView(
        unsigned char const *const data, unsigned const begin_bit,
        unsigned const nibble_count, unsigned const data_bytes) noexcept
        : data_(nibble_count == 0 ? nullptr : data)
        , begin_bit_(nibble_count == 0 ? 0 : static_cast<uint8_t>(begin_bit))
        , nibble_count_(static_cast<size_type>(nibble_count))
        , data_bytes_(nibble_count == 0 ? 0 : static_cast<uint8_t>(data_bytes))
    {
        MONAD_ASSERT(begin_bit < 8);
        MONAD_ASSERT(nibble_count <= std::numeric_limits<size_type>::max());
        MONAD_ASSERT(data_bytes <= std::numeric_limits<uint8_t>::max());
    }

public:
    static constexpr unsigned npos = std::numeric_limits<unsigned>::max();

    constexpr NibblesView() = default;
    constexpr NibblesView(NibblesView const &) = default;
    NibblesView &operator=(NibblesView const &) = default;

    // View over symbols [begin_nibble, end_nibble) of a materialized,
    // left-aligned symbol buffer `data`.
    constexpr explicit NibblesView(
        unsigned const begin_nibble, unsigned const end_nibble,
        unsigned char const *const data) noexcept
        : NibblesView(
              data + (begin_nibble * NIBBLE_BITS) / 8,
              (begin_nibble * NIBBLE_BITS) % 8, end_nibble - begin_nibble,
              bytes_for_nibbles(end_nibble) - (begin_nibble * NIBBLE_BITS) / 8)
    {
        MONAD_ASSERT(
            begin_nibble <= end_nibble &&
            end_nibble <= std::numeric_limits<size_type>::max());
    }

    // View over a raw byte string with data_bytes bytes starting at `data`,
    // whose symbols start `begin_bit` bits into data[0]. Used by Node.
    static constexpr NibblesView from_bits(
        unsigned char const *const data, unsigned const begin_bit,
        unsigned const nibble_count, unsigned const data_bytes) noexcept
    {
        return NibblesView{data, begin_bit, nibble_count, data_bytes};
    }

    // constructor from byte_string_view: the bytes are reinterpreted as a
    // left-aligned symbol string of nibbles_for_bytes(size) symbols
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(byte_string_view const &s) noexcept
        : NibblesView(
              s.data(), 0, nibbles_for_bytes(s.size()),
              static_cast<unsigned>(s.size()))
    {
        MONAD_ASSERT(
            nibbles_for_bytes(s.size()) <=
            std::numeric_limits<size_type>::max());
    }

    // constructor from byte_string
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(byte_string const &s) noexcept
        : NibblesView(byte_string_view{s})
    {
    }

    // constructor from a 32-byte hash, viewed as nibbles_for_bytes(32) symbols
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(monad_hash256 const &h) noexcept
        : NibblesView(
              h.bytes, 0, nibbles_for_bytes(sizeof(h.bytes)), sizeof(h.bytes))
    {
    }

    // constructor from Nibbles
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(Nibbles const &n) noexcept
        : NibblesView(n.data(), n.begin_bit_, n.nibble_count_, n.data_size())
    {
    }

    unsigned char const *data() const noexcept
    {
        return data_;
    }

    [[nodiscard]] bool empty() const noexcept
    {
        return !data_;
    }

    // true when symbol 0 does not start on a byte boundary
    bool begin_nibble() const noexcept
    {
        return begin_bit_ != 0;
    }

    // bytes needed to materialize the symbols, including the leading
    // alignment bits and the trailing padding bits (>= data_span().size())
    constexpr unsigned data_size() const
    {
        return nibble_count_ == 0
                   ? 0
                   : bytes_for_bits(begin_bit_ + nibble_count_ * NIBBLE_BITS);
    }

    // the bytes actually backing this view
    std::span<unsigned char const> data_span() const noexcept
    {
        return {data_, std::min<unsigned>(data_bytes_, data_size())};
    }

    constexpr size_type nibble_size() const
    {
        return nibble_count_;
    }

    constexpr NibblesView
    substr(unsigned const pos, unsigned const count = npos) const
    {
        MONAD_ASSERT(pos <= nibble_size());
        MONAD_ASSERT(count == npos || count <= (nibble_size() - pos));
        unsigned const bit = begin_bit_ + pos * NIBBLE_BITS;
        unsigned const skip_bytes = bit / 8;
        return NibblesView{
            data_ + skip_bytes,
            bit % 8,
            count == npos ? nibble_size() - pos : count,
            data_bytes_ > skip_bytes ? data_bytes_ - skip_bytes : 0};
    }

    bool starts_with(NibblesView const other) const
    {
        if (nibble_size() < other.nibble_size()) {
            return false;
        }
        return substr(0, other.nibble_size()) == other;
    }

    [[nodiscard]] unsigned char get(unsigned const i) const
    {
        MONAD_ASSERT(i < nibble_size());
        return detail::get_symbol(data_, begin_bit_, i, data_bytes_);
    }
};

static_assert(sizeof(NibblesView) == 16);
static_assert(alignof(NibblesView) == 8);
static_assert(std::is_trivially_copyable_v<NibblesView> == true);

inline Nibbles::Nibbles(NibblesView const nibbles)
{
    begin_bit_ = nibbles.begin_bit_;
    nibble_count_ = nibbles.nibble_count_;
    if (nibble_count_ != 0) {
        auto const size = nibbles.data_size();
        auto const backed = nibbles.data_span();
        data_ = std::make_unique<unsigned char[]>(size);
        std::memcpy(data_.get(), backed.data(), backed.size());
        if (backed.size() < size) {
            std::memset(data_.get() + backed.size(), 0, size - backed.size());
        }
    }
}

constexpr bool operator==(NibblesView const &a, NibblesView const &b)
{
    if (&a == &b) {
        return true;
    }
    if (a.nibble_size() != b.nibble_size()) {
        return false;
    }
    for (auto i = 0u; i < a.nibble_size(); ++i) {
        if (a.get(i) != b.get(i)) {
            return false;
        }
    }
    return true;
}

constexpr std::strong_ordering
operator<=>(NibblesView const &a, NibblesView const &b)
{
    unsigned const min_size = std::min(a.nibble_size(), b.nibble_size());
    for (unsigned i = 0; i < min_size; ++i) {
        if (a.get(i) != b.get(i)) {
            return a.get(i) <=> b.get(i);
        }
    }
    return a.nibble_size() <=> b.nibble_size();
}

template <class... Args>
    requires(
        (std::same_as<Args, unsigned char> || std::same_as<Args, NibblesView>),
        ...)
constexpr Nibbles concat(Args... args)
{
    unsigned num_nibbles = 0;
    (
        [&num_nibbles]<class T>(T const arg) {
            if constexpr (std::same_as<T, unsigned char>) {
                ++num_nibbles;
            }
            else {
                num_nibbles += arg.nibble_size();
            }
        }(args),
        ...);

    Nibbles ret{num_nibbles};
    unsigned index = 0;
    (
        [&ret, &index]<class T>(T const arg) {
            if constexpr (std::same_as<T, unsigned char>) {
                ret.set(index, arg);
                ++index;
            }
            else {
                for (auto i = 0u; i < arg.nibble_size(); ++i) {
                    ret.set(index + i, arg.get(i));
                }
                index += arg.nibble_size();
            }
        }(args),
        ...);
    return ret;
}

constexpr Nibbles
Nibbles::substr(unsigned const pos, unsigned const count) const
{
    auto const ret = concat(NibblesView(*this).substr(pos, count));
    MONAD_ASSERT(ret.begin_bit_ == 0);
    return ret;
}

// Recover the byte string a left-aligned symbol string was expanded from
// (inverse of NibblesView(byte_string_view)); the padding bits are dropped.
inline byte_string nibbles_to_bytes(NibblesView const nibbles)
{
    unsigned const nbytes = bytes_from_nibbles(nibbles.nibble_size());
    if (!nibbles.begin_nibble()) {
        MONAD_ASSERT(nibbles.data_span().size() >= nbytes);
        return byte_string{nibbles.data(), nbytes};
    }
    Nibbles const aligned = concat(nibbles);
    MONAD_ASSERT(aligned.data_size() >= nbytes);
    return byte_string{aligned.data(), nbytes};
}

inline std::ostream &operator<<(std::ostream &s, NibblesView const &v)
{
    if (v.empty()) {
        return s << "(empty)";
    }
    auto const oldwidth = int(s.width());
    s.width(2);
    s << "0x" << std::hex;
    for (NibblesView::size_type n = 0; n < v.nibble_size(); n++) {
        s << static_cast<uint32_t>(v.get(n));
    }
    s.width(oldwidth);
    return s << std::dec;
}

inline std::ostream &operator<<(std::ostream &s, Nibbles const &v)
{
    return s << NibblesView(v);
}

MONAD_MPT_NAMESPACE_END
