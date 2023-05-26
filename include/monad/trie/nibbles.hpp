#pragma once

#include <limits>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <monad/trie/config.hpp>
#include <monad/trie/nibbles_view.hpp>
#include <monad/trie/util.hpp>

#include <cassert>
#include <cstring>
#include <string>

MONAD_TRIE_NAMESPACE_BEGIN

namespace impl
{
    template <typename TNibbles>
    constexpr void copy_from_nibbles(byte_string &dest, TNibbles const &nibbles)
    {
        for (size_t i = 0; i < nibbles.size(); i += 2) {
            assert(nibbles[i] <= 0xF);

            auto const left =
                static_cast<byte_string::value_type>(nibbles[i] << 4);
            if (i == (nibbles.size() - 1)) {
                dest.push_back(left);
                break;
            }
            dest.push_back(left | nibbles[i + 1]);
        }
    }
}

struct Nibbles
{
    byte_string rep;

    static constexpr uint8_t MAX_SIZE = 64;

    constexpr Nibbles()
        : rep(1, 0)
    {
    }
    constexpr Nibbles(Nibbles const &) = default;
    constexpr Nibbles(Nibbles &&) = default;
    constexpr Nibbles &operator=(Nibbles const &) = default;

    constexpr explicit Nibbles(byte_string_view nibbles)
    {
        assert(nibbles.size() <= MAX_SIZE);

        rep.push_back(static_cast<byte_string::value_type>(nibbles.size()));

        impl::copy_from_nibbles(rep, nibbles);
    }

    constexpr explicit Nibbles(bytes32_t const &b32)
    {
        static_assert(sizeof(bytes32_t) * 2 == MAX_SIZE);
        rep.push_back(MAX_SIZE);
        rep.append(b32.bytes, sizeof(bytes32_t));
    }

    constexpr explicit Nibbles(NibblesView const &nibbles)
    {
        rep.push_back(nibbles.size());

        if (nibbles.start % 2) {
            impl::copy_from_nibbles(rep, nibbles);
        }
        else {
            bool const is_odd = nibbles.size() % 2;
            rep.append(
                &nibbles.rep[nibbles.start / 2 + 1],
                nibbles.size() / 2 + is_odd);

            constexpr std::array<uint8_t, 2> masks = {0xFF, 0xF0};
            rep.back() &= masks[is_odd];
        }
    }

    [[nodiscard]] constexpr byte_string::value_type operator[](uint8_t i) const
    {
        assert(i < size());
        return get_nibble(rep, i);
    }

    [[nodiscard]] constexpr uint8_t size() const
    {
        assert(!rep.empty());
        return rep.front();
    }

    [[nodiscard]] constexpr bool empty() const { return size() == 0; }

    [[nodiscard]] constexpr NibblesView substr(uint8_t pos) const
    {
        assert(pos <= size());
        return NibblesView{
            rep, pos, static_cast<byte_string::value_type>(size() - pos)};
    }

    [[nodiscard]] constexpr NibblesView prefix(uint8_t n) const
    {
        assert(n <= size());
        return {rep, 0, n};
    }

    constexpr void push_back(byte_string::value_type nibble)
    {
        assert(nibble <= 0xF);
        assert(!rep.empty());

        if (size() % 2) {
            rep.back() |= nibble;
        }
        else {
            rep.push_back(static_cast<byte_string::value_type>(nibble << 4));
        }
        ++rep[0];
    }

    constexpr void pop_back()
    {
        assert(!empty());

        if (size() % 2) {
            rep.pop_back();
        }
        else {
            rep.back() &= 0xF0; // zero out last nibble
        }

        --rep[0];
    }

    [[nodiscard]] constexpr bool startswith(Nibbles const &prefix) const
    {
        if (prefix.size() > size()) {
            return false;
        }

        size_t const i = prefix.size() / 2;
        if (std::memcmp(&rep[1], &prefix.rep[1], i) != 0) {
            return false;
        }

        if (prefix.size() % 2) {
            return (rep[i + 1] & 0xF0) == (prefix.rep[i + 1] & 0xF0);
        }

        return true;
    }

    [[nodiscard]] constexpr operator NibblesView() const
    {
        return {rep, 0, size()};
    }

    [[nodiscard]] constexpr Nibbles operator+(Nibbles const &rhs) const
    {
        if (empty()) {
            return rhs;
        }

        if (rhs.empty()) {
            return *this;
        }

        Nibbles ret = *this;

        if (ret.size() % 2) {
            ret.rep.back() |= rhs.rep[1] >> 4;
            impl::copy_from_nibbles(ret.rep, rhs.substr(1));
        }
        else {
            ret.rep.append(&rhs.rep[1], rhs.rep.size() - 1);
        }

        ret.rep[0] += rhs.size();

        return ret;
    }

    // lexicographic comparison
    [[nodiscard]] constexpr int compare(Nibbles const &other) const
    {
        if (size() == other.size()) {
            return std::memcmp(&rep[0], &other.rep[0], rep.size());
        }

        size_t const min_size = std::min(size(), other.size());

        size_t const i = min_size / 2;
        auto rc = std::memcmp(&rep[1], &other.rep[1], i);
        if (rc != 0) {
            return rc;
        }

        if (min_size % 2) {
            uint8_t const b1 = rep[i + 1] & 0xF0;
            uint8_t const b2 = other.rep[i + 1] & 0xF0;

            rc = std::memcmp(&b1, &b2, 1);
            if (rc != 0) {
                return rc;
            }
        }

        return size() - other.size();
    }

    [[nodiscard]] constexpr bool operator==(Nibbles const &) const = default;

    [[nodiscard]] constexpr auto operator<=>(Nibbles const &rhs) const
    {
        return compare(rhs) <=> 0;
    }

    [[nodiscard]] constexpr bool operator==(NibblesView const &view) const
    {
        if (size() != view.size()) {
            return false;
        }

        if (view.start % 2) {
            for (uint8_t i = 0; i < size(); ++i) {
                if ((*this)[i] != view[i]) {
                    return false;
                }
            }
            return true;
        }
        else {
            size_t const i = size() / 2;
            size_t const vs = view.start / 2 + 1;
            auto const rc = std::memcmp(&rep[1], &view.rep[vs], i);
            if (rc != 0 || (size() % 2) == 0) {
                return rc == 0;
            }

            return (rep.back() & 0xF0) == (view.rep[vs + i] & 0xF0);
        }
    }
};

[[nodiscard]] constexpr std::pair<Nibbles, size_t>
deserialize_nibbles(byte_string_view bytes)
{
    MONAD_ASSERT(!bytes.empty());

    std::pair<Nibbles, size_t> ret;

    auto &[nibbles, num_bytes] = ret;
    num_bytes = 1 + bytes[0] / 2 + (bytes[0] % 2);

    MONAD_ASSERT(bytes.size() >= num_bytes);

    nibbles.rep = byte_string(bytes.data(), num_bytes);

    return ret;
}

constexpr void serialize_nibbles(byte_string &buffer, Nibbles const &nibbles)
{
    buffer.append(nibbles.rep);
}

[[nodiscard]] constexpr uint8_t
longest_common_prefix_size(Nibbles const &first, Nibbles const &second)
{
    auto const size =
        static_cast<uint8_t>(std::min(first.size(), second.size()));
    for (uint8_t i = 0; i < size; ++i) {
        if (first[i] != second[i]) {
            return i;
        }
    }
    return size;
}

static_assert(sizeof(Nibbles) == 32);
static_assert(alignof(Nibbles) == 8);

MONAD_TRIE_NAMESPACE_END
