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
#include <concepts>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>
#include <memory>
#include <span>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

class Nibbles;
class NibblesView;
class Node;

constexpr bool operator==(NibblesView const &a, NibblesView const &b);
constexpr std::strong_ordering
operator<=>(NibblesView const &a, NibblesView const &b);

// One argument of concat: a single nibble, or anything viewable as nibbles.
template <class T>
concept NibblesPiece = std::same_as<std::remove_cvref_t<T>, unsigned char> ||
                       std::convertible_to<T const &, NibblesView>;

template <NibblesPiece... Args>
constexpr Nibbles concat(Args const &...args);

class Nibbles
{
private:
    friend class NibblesView;
    template <NibblesPiece... Args>
    friend constexpr Nibbles concat(Args const &...args);
    using size_type = uint8_t; // max length support is 255 nibbles
    std::unique_ptr<unsigned char[]> data_;
    bool begin_nibble_{false};
    size_type end_nibble_{0};

public:
    static constexpr unsigned npos = std::numeric_limits<unsigned>::max();

    constexpr Nibbles() = default;

    Nibbles(Nibbles &&) = default;

    Nibbles &operator=(Nibbles &&) = default;

    explicit Nibbles(size_t const end_nibble)
        : data_(std::make_unique<unsigned char[]>((end_nibble + 1) / 2))
        , begin_nibble_(false)
        , end_nibble_(static_cast<size_type>(end_nibble))
    {
        MONAD_ASSERT(end_nibble <= std::numeric_limits<size_type>::max());
#ifdef __clang_analyzer__ // false positive
        memset(data_.get(), 0, (end_nibble + 1) / 2);
#endif
    }

    Nibbles(NibblesView other); // NOLINT(google-explicit-constructor)

    Nibbles(Nibbles const &other)
    {
        begin_nibble_ = other.begin_nibble_;
        end_nibble_ = other.end_nibble_;
        if (begin_nibble_ != end_nibble_) {
            data_ = std::make_unique<unsigned char[]>(other.data_size());
            std::memcpy(data_.get(), other.data_.get(), other.data_size());
        }
    }

    Nibbles &operator=(Nibbles const &other)
    {
        if (this != &other) {
            begin_nibble_ = other.begin_nibble_;
            end_nibble_ = other.end_nibble_;
            if (begin_nibble_ != end_nibble_) {
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

    bool begin_nibble() const noexcept
    {
        return begin_nibble_;
    }

    [[nodiscard]] bool empty() const noexcept
    {
        return !data_;
    }

    constexpr unsigned data_size() const noexcept
    {
        return (static_cast<size_type>(begin_nibble_) == end_nibble_)
                   ? 0
                   : ((end_nibble_ + 1) / 2);
    }

    constexpr size_type nibble_size() const
    {
        return end_nibble_ - static_cast<size_type>(begin_nibble_);
    }

    // Returns a left-aligned Nibbles containing a subrange of nibbles starting
    // at `pos` and up to `count` nibbles (or to the end if count == npos).
    // The returned Nibbles is always left-aligned (begin_nibble_ == 0).
    constexpr Nibbles substr(unsigned pos, unsigned count = npos) const;

    [[nodiscard]] unsigned char get(unsigned const i) const
    {
        MONAD_ASSERT(i < nibble_size());
        return ::get_nibble(data_.get(), begin_nibble_ + i);
    }

    constexpr void set(unsigned const i, unsigned char const value)
    {
        MONAD_ASSERT(value <= 0xF);
        MONAD_ASSERT(
            i < static_cast<unsigned>(
                    end_nibble_ - static_cast<size_type>(begin_nibble_)));
        ::set_nibble(data_.get(), begin_nibble_ + i, value);
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
    bool begin_nibble_{false};
    size_type end_nibble_{0};

public:
    static constexpr unsigned npos = std::numeric_limits<unsigned>::max();

    constexpr NibblesView() = default;
    constexpr NibblesView(NibblesView const &) = default;
    NibblesView &operator=(NibblesView const &) = default;

    constexpr explicit NibblesView(
        unsigned const begin_nibble, unsigned const end_nibble,
        unsigned char const *const data) noexcept
        : data_(
              (begin_nibble == end_nibble) ? nullptr
                                           : (data + begin_nibble / 2))
        , begin_nibble_(data_ == nullptr ? false : (begin_nibble & 1))
        , end_nibble_(
              data_ == nullptr ? 0
                               : static_cast<size_type>(
                                     end_nibble - begin_nibble + begin_nibble_))
    {
        MONAD_ASSERT(
            begin_nibble <= end_nibble &&
            end_nibble <= std::numeric_limits<size_type>::max());
    }

    // constructor from byte_string_view
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(byte_string_view const &s) noexcept
        : NibblesView(false, static_cast<uint8_t>(2 * s.size()), s.data())
    {
        MONAD_ASSERT((s.size() * 2) <= std::numeric_limits<size_type>::max());
    }

    // constructor from byte_string
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(byte_string const &s) noexcept
        : NibblesView(byte_string_view{s})
    {
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(monad_hash256 const &h) noexcept
        : NibblesView(0, 2 * sizeof(h.bytes), h.bytes)
    {
    }

    // construct from Nibbles
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr NibblesView(Nibbles const &n) noexcept
        : NibblesView{n.begin_nibble_, n.end_nibble_, n.data_.get()}
    {
    }

    unsigned char const *data() const noexcept
    {
        return data_;
    }

    bool begin_nibble() const noexcept
    {
        return begin_nibble_;
    }

    [[nodiscard]] bool empty() const noexcept
    {
        return !data_;
    }

    // size of data in bytes
    constexpr unsigned data_size() const
    {
        return (static_cast<size_type>(begin_nibble_) == end_nibble_)
                   ? 0
                   : ((end_nibble_ + 1) / 2);
    }

    std::span<unsigned char const> data_span() const noexcept
    {
        return {data_, data_size()};
    }

    constexpr size_type nibble_size() const
    {
        return end_nibble_ - static_cast<size_type>(begin_nibble_);
    }

    constexpr NibblesView
    substr(unsigned const pos, unsigned const count = npos) const
    {
        MONAD_ASSERT(count == npos || count <= (nibble_size() - pos));
        auto const begin_nibble = static_cast<unsigned>(begin_nibble_) + pos;
        return NibblesView{
            begin_nibble,
            count == npos ? end_nibble_ : (begin_nibble + count),
            data_};
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
        return get_nibble(data_, begin_nibble_ + i);
    }
};

static_assert(sizeof(NibblesView) == 16);
static_assert(alignof(NibblesView) == 8);
static_assert(std::is_trivially_copyable_v<NibblesView> == true);

inline Nibbles::Nibbles(NibblesView const nibbles)
{
    begin_nibble_ = nibbles.begin_nibble_;
    end_nibble_ = nibbles.end_nibble_;
    if (begin_nibble_ != end_nibble_) {
        data_ = std::make_unique<unsigned char[]>(nibbles.data_size());
        std::memcpy(data_.get(), nibbles.data_, nibbles.data_size());
    }
}

namespace detail
{
    // Compares the first `n` nibbles of two views that start at the same
    // parity. Nibbles are packed high half first, so whole bytes order the
    // same way as the nibbles in them.
    constexpr std::strong_ordering
    compare_aligned_prefix(NibblesView const a, NibblesView const b, unsigned n)
    {
        if (n == 0) {
            return std::strong_ordering::equal;
        }
        unsigned char const *pa = a.data();
        unsigned char const *pb = b.data();
        if (a.begin_nibble()) {
            auto const x = static_cast<unsigned char>(*pa & 0xF);
            auto const y = static_cast<unsigned char>(*pb & 0xF);
            if (x != y) {
                return x <=> y;
            }
            ++pa;
            ++pb;
            --n;
        }
        unsigned const bytes = n / 2;
        if (bytes != 0) {
            int const c = std::memcmp(pa, pb, bytes);
            if (c != 0) {
                return c <=> 0;
            }
        }
        if (n % 2 != 0) {
            return (pa[bytes] >> 4) <=> (pb[bytes] >> 4);
        }
        return std::strong_ordering::equal;
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
    if (a.begin_nibble() == b.begin_nibble()) {
        return detail::compare_aligned_prefix(a, b, a.nibble_size()) == 0;
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
    if (a.begin_nibble() == b.begin_nibble()) {
        auto const cmp = detail::compare_aligned_prefix(a, b, min_size);
        if (cmp != 0) {
            return cmp;
        }
        return a.nibble_size() <=> b.nibble_size();
    }
    for (unsigned i = 0; i < min_size; ++i) {
        if (a.get(i) != b.get(i)) {
            return a.get(i) <=> b.get(i);
        }
    }
    return a.nibble_size() <=> b.nibble_size();
}

// Writes `src` into `dest` starting at nibble `dest_nibble`. The half-byte
// before an odd `dest_nibble` is preserved; if the write ends mid-byte, the
// rest of that byte is zeroed. The caller guarantees the room.
constexpr void copy_nibbles(
    unsigned char *const dest, unsigned const dest_nibble,
    NibblesView const src) noexcept
{
    unsigned const end = src.begin_nibble() + src.nibble_size();
    unsigned char const *const in = src.data();
    unsigned char *out = dest + dest_nibble / 2;
    unsigned i = src.begin_nibble();
    if (i == end) {
        return;
    }
    if (dest_nibble % 2 != 0) {
        *out = static_cast<unsigned char>((*out & 0xF0) | get_nibble(in, i));
        ++out;
        ++i;
    }
    if (i % 2 == 0) {
        unsigned const bytes = (end - i) / 2;
        std::memcpy(out, in + i / 2, bytes);
        out += bytes;
        i += 2 * bytes;
    }
    else {
        for (; i + 1 < end; i += 2) {
            *out++ = static_cast<unsigned char>(
                (in[i / 2] << 4) | (in[i / 2 + 1] >> 4));
        }
    }
    if (i < end) {
        *out = static_cast<unsigned char>(get_nibble(in, i) << 4);
    }
}

namespace detail
{
    template <NibblesPiece T>
    constexpr unsigned piece_nibble_size(T const &piece)
    {
        if constexpr (std::same_as<T, unsigned char>) {
            return 1;
        }
        else {
            return NibblesView{piece}.nibble_size();
        }
    }

    template <NibblesPiece T>
    constexpr void
    write_piece(unsigned char *const dest, unsigned &index, T const &piece)
    {
        if constexpr (std::same_as<T, unsigned char>) {
            MONAD_ASSERT(piece <= 0xF);
            set_nibble(dest, index, piece);
            ++index;
        }
        else {
            NibblesView const view{piece};
            copy_nibbles(dest, index, view);
            index += view.nibble_size();
        }
    }
}

template <NibblesPiece... Args>
constexpr Nibbles concat(Args const &...args)
{
    Nibbles ret{(0u + ... + detail::piece_nibble_size(args))};
    unsigned index = 0;
    (detail::write_piece(ret.data_.get(), index, args), ...);
    return ret;
}

constexpr Nibbles
Nibbles::substr(unsigned const pos, unsigned const count) const
{
    auto const ret = concat(NibblesView(*this).substr(pos, count));
    MONAD_ASSERT(ret.begin_nibble_ == 0);
    return ret;
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
