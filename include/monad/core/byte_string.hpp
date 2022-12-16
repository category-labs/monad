#pragma once

#include <monad/config.hpp>

#include <array>
#include <cstddef>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

using byte_string = std::basic_string<unsigned char>;

template <size_t N>
using byte_string_fixed = std::array<unsigned char, N>;

using byte_string_view = std::basic_string_view<unsigned char>;

MONAD_NAMESPACE_END
