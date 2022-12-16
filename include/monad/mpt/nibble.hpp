#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <cstddef>
#include <cassert>
#include <string>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

class Nibble
{
private:
    byte_string::value_type nibble_;

public:
    constexpr Nibble() = default;

    constexpr explicit Nibble(byte_string::value_type nibble)
        : nibble_(nibble & 0x0f)
    {
        // Valid range for nibbles is [0x0, 0xf]
        assert((nibble & 0xf0) == 0x00);
    }

    constexpr bool operator==(Nibble const&) const = default;

    // implicit conversion to underlying type allowed
    constexpr operator byte_string::value_type() const
    {
        return nibble_;
    }
};

using Nibbles = std::basic_string<Nibble>;
} // namespace mpt

MONAD_NAMESPACE_END
