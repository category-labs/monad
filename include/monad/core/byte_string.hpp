#pragma once

#include <monad/config.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

using byte_string = std::basic_string<unsigned char>;

template <size_t N>
using byte_string_fixed = std::array<unsigned char, N>;

using byte_string_view = std::basic_string_view<unsigned char>;

using byte_string_loc = uint64_t;

const byte_string_loc max_byte_string_loc = ~0u;

template <size_t N>
byte_string_view to_byte_string_view(unsigned char const (&a)[N])
{
    return {&a[0], N};
}

template <class T, size_t N>
byte_string_view to_byte_string_view(std::array<T, N> const &a)
{
    return {a.data(), N};
}

inline byte_string_view to_byte_string_view(std::string const &s)
{
    return {reinterpret_cast<unsigned char const *>(&s[0]), s.size()};
}

MONAD_NAMESPACE_END
