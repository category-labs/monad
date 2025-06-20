// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

/**
 * @file
 *
 * A C++20 equivalent of the BSD <err.h> header; uses std::error_condition
 * instead of errno and <format> instead of printf
 */

#include <cerrno>
#include <cstdlib>
#include <format>
#include <print>
#include <system_error>

#include <stdio.h>

extern char const *__progname;

template <typename... Args>
[[noreturn]] void errc_f(
    int eval, std::error_condition const &ec, std::format_string<Args...> fmt,
    Args &&...args)
{
    std::print(stderr, "{}: ", __progname);
    std::print(stderr, fmt, std::forward<Args>(args)...);
    if (ec) {
        std::println(stderr, ": {} [{}]", ec.message(), ec.value());
    }
    else {
        std::println(stderr);
    }
    std::exit(eval);
}

template <typename... Args>
[[noreturn]] void errc_f(
    int eval, int errno_code, std::format_string<Args...> fmt, Args &&...args)
{
    errc_f(
        eval,
        static_cast<std::errc>(errno_code),
        fmt,
        std::forward<Args>(args)...);
}

template <typename... Args>
[[noreturn]] void
err_f(int eval, std::format_string<Args...> fmt, Args &&...args)
{
    errc_f(
        eval, static_cast<std::errc>(errno), fmt, std::forward<Args>(args)...);
}

template <typename... Args>
[[noreturn]] void
errx_f(int eval, std::format_string<Args...> fmt, Args &&...args)
{
    errc_f(eval, {}, fmt, std::forward<Args>(args)...);
}

#define EX_SET_OR_RETURN(X, INIT)                                              \
    if (auto ex = (INIT)) {                                                    \
        (X) = *ex;                                                             \
    }                                                                          \
    else {                                                                     \
        return ex.error();                                                     \
    }
