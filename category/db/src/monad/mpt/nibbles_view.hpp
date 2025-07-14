#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/core/nibble.h>
#include <monad/mpt/config.hpp>

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>
#include <memory>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

class NibblesView;
class Node;

class Nibbles
{
private:
    friend class NibblesView;
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
        MONAD_DEBUG_ASSERT(end_nibble <= std::numeric_limits<size_type>::max());
#ifdef __clang_analyzer__ // false positive
        memset(data_.get(), 0, (end_nibble + 1) / 2);
#endif
    }

    Nibbles(NibblesView other);

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
    inline constexpr Nibbles
    substr(unsigned const pos, unsigned const count = npos) const;

    inline constexpr bool operator==(NibblesView const &other) const;
    inline constexpr auto operator<=>(NibblesView const &other) const;

    [[nodiscard]] unsigned char get(unsigned const i) const
    {
        MONAD_ASSERT(i < nibble_size());
        return get_nibble(data_.get(), begin_nibble_ + i);
    }

    constexpr void set(unsigned const i, unsigned char const value)
    {
        MONAD_DEBUG_ASSERT(value <= 0xF);
        MONAD_DEBUG_ASSERT(
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
        MONAD_DEBUG_ASSERT(
            begin_nibble <= end_nibble &&
            end_nibble <= std::numeric_limits<size_type>::max());
    }

    // constructor from byte_string_view
    constexpr NibblesView(byte_string_view const &s) noexcept
        : NibblesView(false, static_cast<uint8_t>(2 * s.size()), s.data())
    {
        MONAD_DEBUG_ASSERT(
            (s.size() * 2) <= std::numeric_limits<size_type>::max());
    }

    // constructor from byte_string
    constexpr NibblesView(byte_string const &s) noexcept
        : NibblesView(byte_string_view{s})
    {
    }

    constexpr NibblesView(hash256 const &h) noexcept
        : NibblesView(0, 2 * sizeof(h.bytes), h.bytes)
    {
    }

    // construct from Nibbles
    constexpr NibblesView(Nibbles const &n) noexcept
        : NibblesView{n.begin_nibble_, n.end_nibble_, n.data_.get()}
    {
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

    constexpr size_type nibble_size() const
    {
        return end_nibble_ - static_cast<size_type>(begin_nibble_);
    }

    constexpr NibblesView
    substr(unsigned const pos, unsigned const count = npos) const
    {
        MONAD_DEBUG_ASSERT(count == npos || count <= (nibble_size() - pos));
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

    constexpr bool operator==(NibblesView const &other) const
    {
        if (this == &other) {
            return true;
        }

        if (nibble_size() != other.nibble_size()) {
            return false;
        }

        if (nibble_size()) {
            MONAD_DEBUG_ASSERT(data_ && other.data_);
            for (auto i = 0u; i < nibble_size(); ++i) {
                if (get(i) != other.get(i)) {
                    return false;
                }
            }
        }
        return true;
    }

    constexpr auto operator<=>(NibblesView const &other) const
    {
        unsigned const min_size = std::min(nibble_size(), other.nibble_size());
        for (unsigned i = 0; i < min_size; ++i) {
            if (get(i) != other.get(i)) {
                return get(i) <=> other.get(i);
            }
        }
        return nibble_size() <=> other.nibble_size();
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

inline constexpr bool Nibbles::operator==(NibblesView const &other) const
{
    return NibblesView(*this) == other;
}

inline constexpr auto Nibbles::operator<=>(NibblesView const &other) const
{
    return NibblesView(*this) <=> other;
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

inline constexpr Nibbles
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
