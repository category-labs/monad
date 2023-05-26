#pragma once

#include <monad/trie/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/trie/nibbles.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

// A key is composed of a prefix and a path. This class helps facilitate
// manipulation of a key.
struct KeyBuffer
{
    constexpr static size_t MAX_PATH_SIZE = 1 + Nibbles::MAX_SIZE / 2;
    constexpr static size_t MAX_SIZE = sizeof(address_t) + MAX_PATH_SIZE;

    byte_string_fixed<MAX_SIZE> raw;
    size_t buf_size = 0;
    size_t prefix_size = 0;

    [[nodiscard]] constexpr byte_string_view prefix() const
    {
        return {&raw[0], prefix_size};
    }
    [[nodiscard]] constexpr byte_string_view view() const
    {
        return {&raw[0], buf_size};
    }

    constexpr void set_prefix(address_t const &address)
    {
        prefix_size = sizeof(address_t);
        buf_size = sizeof(address_t);
        std::copy_n(&address.bytes[0], sizeof(address_t), &raw[0]);
    }

    constexpr void set_path(NibblesView const &nibbles)
    {
        assert(prefix_size == 0 || prefix_size == 20);

        raw[prefix_size] = nibbles.size();

        buf_size = prefix_size + 1;
        if (nibbles.start % 2) {
            for (size_t i = 0; i < nibbles.size(); i += 2) {
                assert(nibbles[i] <= 0xF);

                auto const left =
                    static_cast<byte_string::value_type>(nibbles[i] << 4);
                if (i == (nibbles.size() - 1)) {
                    raw[buf_size] = left;
                    ++buf_size;
                    break;
                }
                raw[buf_size] = left | nibbles[i + 1];
                ++buf_size;
            }
        }
        else {
            bool const is_odd = nibbles.size() % 2;
            size_t const num_bytes = nibbles.size() / 2 + is_odd;

            std::copy_n(
                &nibbles.rep[nibbles.start / 2 + 1], num_bytes, &raw[buf_size]);

            buf_size += num_bytes;

            constexpr std::array<uint8_t, 2> masks = {0xFF, 0xF0};
            raw[buf_size - 1] &= masks[is_odd];
        }
    }

    constexpr void path_pop_back()
    {
        assert(buf_size <= MAX_SIZE);
        assert(buf_size > prefix_size);
        assert(raw[prefix_size]);

        if (raw[prefix_size] % 2) {
            --buf_size;
        }
        else {
            raw[buf_size - 1] &= 0xF0;
        }

        --raw[prefix_size];
    }

    [[nodiscard]] constexpr bool path_empty() const
    {
        assert(buf_size > prefix_size);
        return raw[prefix_size] == 0;
    }
};

template <typename TNibbles>
constexpr void serialize_nibbles(KeyBuffer &buffer, TNibbles &&nibbles)
{
    buffer.set_path(std::forward<TNibbles>(nibbles));
}

MONAD_TRIE_NAMESPACE_END
