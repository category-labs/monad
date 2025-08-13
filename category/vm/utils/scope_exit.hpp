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

#include <concepts>
#include <functional>
#include <type_traits>
#include <utility>

namespace monad::vm::utils
{
    template <typename F>
    class [[nodiscard]] scope_exit
    {
        using StoredFn = std::decay_t<F>;
        static_assert(
            std::invocable<StoredFn &>, "Scope exit code must be invocable!");

    public:
        template <typename G>
        explicit constexpr scope_exit(G &&f) noexcept(
            std::is_nothrow_constructible_v<StoredFn, G &&>)
            : f_(std::forward<G>(f))
            , active_(true)
        {
        }

        constexpr ~scope_exit() noexcept(
            std::is_nothrow_invocable_v<StoredFn &>)
        {
            if (active_) {
                std::invoke(f_);
            }
        }

        constexpr scope_exit(scope_exit &&other) noexcept(
            std::is_nothrow_move_constructible_v<StoredFn>)
            : f_(std::move(other.f_))
            , active_(other.active_)
        {
            other.active_ = false;
        }

        scope_exit(scope_exit const &) = delete;
        scope_exit &operator=(scope_exit const &) = delete;
        scope_exit &operator=(scope_exit &&) = delete;

        constexpr void release() noexcept
        {
            active_ = false;
        }

    private:
        StoredFn f_;
        bool active_;
    };

    template <typename F>
    scope_exit(F &&) -> scope_exit<std::decay_t<F>>;
}
