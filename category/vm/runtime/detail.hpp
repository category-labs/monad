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

#include <category/vm/runtime/types.hpp>

#include <cstddef>
#include <tuple>

namespace monad::vm::runtime::detail
{
    template <typename T>
    struct is_const_pointer : std::false_type
    {
    };

    template <typename T>
    struct is_const_pointer<T const *> : std::true_type
    {
    };

    template <typename T>
    constexpr auto is_const_pointer_v = is_const_pointer<T>::value;

    template <typename T>
    struct is_mut_pointer
    {
        static constexpr auto value =
            std::is_pointer_v<T> && !is_const_pointer_v<T>;
    };

    template <typename T>
    constexpr auto is_mut_pointer_v = is_mut_pointer<T>::value;

    template <typename T>
    struct is_context : std::false_type
    {
    };

    template <>
    struct is_context<Context *> : std::true_type
    {
    };

    template <>
    struct is_context<Context const *> : std::true_type
    {
    };

    template <typename T>
    constexpr auto is_context_v = is_context<T>::value;

    template <size_t N, typename... Args>
    struct make_context_arg_t
    {
        static constexpr std::optional<std::size_t> context_arg{};
    };

    template <size_t N, typename A, typename... Args>
    struct make_context_arg_t<N, A, Args...>
    {
        static constexpr auto context_arg =
            is_context_v<A> ? std::optional<size_t>{N}
                            : make_context_arg_t<N + 1, Args...>::context_arg;
    };

    template <typename... Args>
    struct context_arg_t : make_context_arg_t<0, Args...>
    {
    };

    template <typename T>
    struct is_result
    {
        static constexpr auto value = is_mut_pointer_v<T> && !is_context_v<T>;
    };

    template <typename T>
    constexpr auto is_result_v = is_result<T>::value;

    template <size_t N, typename... Args>
    struct make_result_arg_t
    {
        static constexpr std::optional<std::size_t> result_arg{};
    };

    template <size_t N, typename A, typename... Args>
    struct make_result_arg_t<N, A, Args...>
    {
        static constexpr auto result_arg =
            is_result_v<A> ? std::optional<size_t>{N}
                           : make_result_arg_t<N + 1, Args...>::result_arg;
    };

    template <typename... Args>
    struct result_arg_t : make_result_arg_t<0, Args...>
    {
    };

    template <typename T>
    struct is_remaining_gas : std::is_same<T, std::int64_t>
    {
    };

    template <typename T>
    constexpr auto is_remaining_gas_v = is_remaining_gas<T>::value;

    template <size_t N, typename... Args>
    struct make_remaining_gas_arg_t
    {
        static constexpr std::optional<std::size_t> remaining_gas_arg{};
    };

    template <size_t N, typename A, typename... Args>
    struct make_remaining_gas_arg_t<N, A, Args...>
    {
        static constexpr auto remaining_gas_arg =
            is_remaining_gas_v<A>
                ? std::optional<size_t>{N}
                : make_remaining_gas_arg_t<N + 1, Args...>::remaining_gas_arg;
    };

    template <typename... Args>
    struct remaining_gas_arg_t : make_remaining_gas_arg_t<0, Args...>
    {
    };

    template <typename... Args>
    struct uses_context
    {
        static constexpr auto value =
            context_arg_t<Args...>::context_arg.has_value();
    };

    template <typename... Args>
    constexpr auto uses_context_v = uses_context<Args...>::value;

    template <typename... Args>
    struct uses_result
    {
        static constexpr auto value =
            result_arg_t<Args...>::result_arg.has_value();
    };

    template <typename... Args>
    constexpr auto uses_result_v = uses_result<Args...>::value;

    template <typename... Args>
    struct uses_remaining_gas
    {
        static constexpr auto value =
            remaining_gas_arg_t<Args...>::remaining_gas_arg.has_value();
    };

    template <typename... Args>
    constexpr auto uses_remaining_gas_v = uses_remaining_gas<Args...>::value;
}
