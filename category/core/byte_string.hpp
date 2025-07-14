#pragma once

#include <category/core/config.hpp>

#include <evmc/bytes.hpp>

#include <array>
#include <cstddef>

MONAD_NAMESPACE_BEGIN

using byte_string = evmc::bytes;

template <size_t N>
using byte_string_fixed = std::array<unsigned char, N>;

using byte_string_view = evmc::bytes_view;

template <size_t N>
constexpr byte_string_view to_byte_string_view(unsigned char const (&a)[N])
{
    return {&a[0], N};
}

template <class T, size_t N>
constexpr byte_string_view to_byte_string_view(std::array<T, N> const &a)
{
    return {a.data(), N};
}

inline byte_string_view to_byte_string_view(std::string const &s)
{
    return {reinterpret_cast<unsigned char const *>(&s[0]), s.size()};
}

MONAD_NAMESPACE_END
