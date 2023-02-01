#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>

#include <cassert>

MONAD_TRIE_NAMESPACE_BEGIN

struct Nibbles
{
    bool is_odd;
    byte_string bytes;

    struct FromNibbleArray
    {
    };

    Nibbles(byte_string_view nibbles, FromNibbleArray)
        : is_odd(nibbles.size() % 2)
        , bytes(bytes_from_nibbles(nibbles))
    {
        assert(bytes.size() == (nibbles.size() / 2 + is_odd));
    }

    byte_string::value_type operator[](size_t i) const
    {
        assert(i < size());
        return (i % 2) == 0 ? bytes[i / 2] >> 4 : bytes[i / 2] & 0x0F;
    }

    size_t size() const { return (bytes.size() * 2) - is_odd; }

    bool empty() const { return bytes.empty(); }

    bool operator<(Nibbles const &rhs) const
    {
        auto const min_nibbles_size = std::min(size(), rhs.size());
        auto const min_bytes_size = min_nibbles_size / 2;
        auto const compare =
            bytes.compare(0, min_bytes_size, rhs.bytes, 0, min_bytes_size);
        if (compare > 0) {
            return false;
        }

        if (compare < 0 ||
            ((min_nibbles_size % 2) &&
             (*this)[min_nibbles_size - 1] < rhs[min_nibbles_size - 1])) {
            return true;
        }

        return size() < rhs.size();
    }

    bool operator==(Nibbles const &) const = default;

private:
    byte_string bytes_from_nibbles(byte_string_view nibbles)
    {
        if (nibbles.empty()) {
            return {};
        }

        byte_string ret;
        for (auto it = nibbles.begin(); it < std::prev(nibbles.end());
             std::advance(it, 2)) {
            assert(*it <= 0xF);
            ret.push_back((*it << 4) | *std::next(it));
        }

        if (is_odd) {
            assert(nibbles.back() <= 0xF);
            ret.push_back(nibbles.back() << 4);
        }
        return ret;
    }
};

static_assert(sizeof(Nibbles) == 40);
static_assert(alignof(Nibbles) == 8);

MONAD_TRIE_NAMESPACE_END
