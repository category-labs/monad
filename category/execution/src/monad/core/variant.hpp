#pragma once

#include <monad/config.hpp>

MONAD_NAMESPACE_BEGIN

// shamelessly stolen from cppreference

// helper type for the visitor #4
template <class... Ts>
struct overloaded : Ts...
{
    using Ts::operator()...;
};
// explicit deduction guide (not needed as of C++20)
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

MONAD_NAMESPACE_END
