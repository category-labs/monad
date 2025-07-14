#pragma once

#include <category/core/config.hpp>

#include <array>
#include <cstddef>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    template <class T, size_t... Is, class... Args>
    constexpr std::array<T, sizeof...(Is)>
    make_array_impl(std::index_sequence<Is...>, Args &&...args)
    {
        return {{((void)Is, T{std::forward<Args>(args)...})...}};
    }
}
/*! \brief Return a `std::array<T, N>` with each item constructed
from `args...`. Supports immovable types.
*/
template <class T, size_t N, class... Args>
    requires(std::is_constructible_v<T, Args...>)
constexpr std::array<T, N>
make_array(std::piecewise_construct_t, Args &&...args)
{
    return detail::make_array_impl<T>(
        std::make_index_sequence<N>(), std::forward<Args>(args)...);
}

MONAD_NAMESPACE_END
