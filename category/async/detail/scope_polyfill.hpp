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

/* scope support
(C) 2019 Niall Douglas <http://www.nedproductions.biz/> (3 commits)
File Created: Apr 2019


Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License in the accompanying file
Licence.txt or at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.


Distributed under the Boost Software License, Version 1.0.
    (See accompanying file Licence.txt or copy at
          http://www.boost.org/LICENSE_1_0.txt)
*/

#include "../config.hpp"

#ifndef MONAD_USE_STD_SCOPE
    #if (__cplusplus >= 202000 || _HAS_CXX20) && __has_include(<scope>)
        #define MONAD_USE_STD_SCOPE 1
    #else
        #define MONAD_USE_STD_SCOPE 0
    #endif
#endif

#if MONAD_USE_STD_SCOPE
    #include <scope>
#else
    #include <type_traits>
    #include <utility>
#endif
#include <exception>

namespace monad
{
#if MONAD_USE_STD_SCOPE
    template <class T>
    using scope_exit = std::scope_exit<T>;
    template <class T>
    using scope_fail = std::scope_fail<T>;
    template <class T>
    using scope_success = std::scope_success<T>;
#else
    namespace detail
    {
        template <class T, bool v = noexcept(std::declval<T>()())>
        inline constexpr bool is_nothrow_invocable_(int) noexcept
        {
            return v;
        }

        template <class T>
        inline constexpr bool is_nothrow_invocable_(...) noexcept
        {
            return false;
        }

        template <class T>
        inline constexpr bool is_nothrow_invocable() noexcept
        {
            return is_nothrow_invocable_<typename std::decay<T>::type>(5);
        }

        enum class scope_impl_kind
        {
            exit,
            fail,
            success
        };

        template <class EF, scope_impl_kind kind>
        class scope_impl
        {
            EF _f;
            bool released_{false};
    #if __cplusplus >= 201700 || _HAS_CXX17
            int uncaught_exceptions_;
    #endif

        public:
            scope_impl() = delete;
            scope_impl(scope_impl const &) = delete;
            scope_impl &operator=(scope_impl const &) = delete;
            scope_impl &operator=(scope_impl &&) = delete;

            constexpr scope_impl(scope_impl &&o) noexcept(
                std::is_nothrow_move_constructible<EF>::value)
                : _f(static_cast<EF &&>(o._f))
                , released_(o.released_)
    #if __cplusplus >= 201700 || _HAS_CXX17
                , uncaught_exceptions_(o.uncaught_exceptions_)
    #endif
            {
                o.released_ = true;
            }

            template <
                class T, typename = decltype(std::declval<T>()()),
                typename std::enable_if<
                    !std::is_same<
                        scope_impl, typename std::decay<T>::type>::value //
                        && std::is_constructible<EF, T>::value //
                        && (scope_impl_kind::success == kind ||
                            is_nothrow_invocable<T>()) //
                    ,
                    bool>::type = true>
            explicit constexpr scope_impl(T &&f) noexcept(
                std::is_nothrow_constructible<EF, T>::value)
                : _f(static_cast<T &&>(f))
    #if __cplusplus >= 201700 || _HAS_CXX17
                , uncaught_exceptions_(std::uncaught_exceptions())
    #endif
            {
            }

            ~scope_impl()
            {
                reset();
            }

            constexpr void reset() noexcept
            {
                if (!released_) {
                    released_ = true;
                    if (scope_impl_kind::exit == kind) {
                        _f();
                        return;
                    }
    #if __cplusplus >= 201700 || _HAS_CXX17
                    bool unwind_is_due_to_throw =
                        (std::uncaught_exceptions() > uncaught_exceptions_);
    #else
                    bool unwind_is_due_to_throw = std::uncaught_exception();
    #endif
                    if (scope_impl_kind::fail == kind &&
                        unwind_is_due_to_throw) {
                        _f();
                        return;
                    }
                    if (scope_impl_kind::success == kind &&
                        !unwind_is_due_to_throw) {
                        _f();
                        return;
                    }
                }
            }

            constexpr void release() noexcept
            {
                released_ = true;
            }
        };
    } // namespace detail

    template <class T>
    using scope_exit = detail::scope_impl<T, detail::scope_impl_kind::exit>;
    template <class T>
    using scope_fail = detail::scope_impl<T, detail::scope_impl_kind::fail>;
    template <class T>
    using scope_success =
        detail::scope_impl<T, detail::scope_impl_kind::success>;

    template <
        class T //
    #ifndef _MSC_VER
        ,
        typename = decltype(std::declval<T>()()), // MSVC chokes on these
                                                  // constraints here yet is
        typename std::enable_if<detail::is_nothrow_invocable<T>(), bool>::
            type // perfectly fine with them on the
                 // constructor above :(
        = true
    #endif
        >
    inline constexpr auto make_scope_exit(T &&v)
    {
        return scope_exit<typename std::decay<T>::type>(static_cast<T &&>(v));
    }
    template <
        class T //
    #ifndef _MSC_VER
        ,
        typename = decltype(std::declval<T>()()), //
        typename std::enable_if<
            detail::is_nothrow_invocable<T>(), bool>::type //
        = true
    #endif
        >
    inline constexpr auto make_scope_fail(T &&v)
    {
        return scope_fail<typename std::decay<T>::type>(static_cast<T &&>(v));
    }
    template <
        class T //
    #ifndef _MSC_VER
        ,
        typename = decltype(std::declval<T>()())
    #endif
        >
    inline constexpr auto make_scope_success(T &&v)
    {
        return scope_success<typename std::decay<T>::type>(
            static_cast<T &&>(v));
    }
#endif

}
