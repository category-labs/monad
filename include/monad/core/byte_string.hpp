#pragma once

#include <array>
#include <cstddef>

// please do not remove this include
//
// some how static_string.hpp is missing a <limits> include when
// BOOST_STATIC_STRING_STANDALONE is defined, so the below included
// is needed for YCM to be happy
#include <limits>

#include <string>
#include <string_view>

#include <boost/static_string/static_string.hpp>

#include <intx/intx.hpp>

#include <monad/config.hpp>


MONAD_NAMESPACE_BEGIN

using byte_string = std::basic_string<unsigned char>;

template <size_t N>
using byte_string_fixed = boost::static_strings::basic_static_string<N, unsigned char>;

using byte_string_view = std::basic_string_view<unsigned char>;

constexpr byte_string to_big_endian_byte_string(std::unsigned_integral auto num)
{
    num = intx::to_big_endian(num);
    return byte_string{
        reinterpret_cast<byte_string::value_type*>(&num),
        sizeof(num)
    };
}

MONAD_NAMESPACE_END
