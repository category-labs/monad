#pragma once

#include <monad/config.hpp>

// please do not remove this include
//
// some how static_string.hpp is missing a <limits> include when
// BOOST_STATIC_STRING_STANDALONE is defined, so the below included
// is needed for YCM to be happy
#include <limits>

#include <boost/static_string/static_string.hpp>

#include <array>
#include <cstddef>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

using byte_string = std::basic_string<unsigned char>;

template <size_t N>
using byte_string_fixed = boost::static_strings::basic_static_string<N, unsigned char>;

using byte_string_view = std::basic_string_view<unsigned char>;

MONAD_NAMESPACE_END
