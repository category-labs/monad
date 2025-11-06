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

#include <category/mpt/config.hpp>

#include <category/core/assert.h>

#include <compare>
#include <concepts>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
#if BITINT_MAXWIDTH > 0
    using unsigned_20 = unsigned _BitInt(20);
#else
    class unsigned_20
    {
        uint32_t v_;

    public:
        // NOLINTNEXTLINE(google-explicit-constructor)
        constexpr unsigned_20(uint32_t v)
            : v_(v & 0xfffff)
        {
            MONAD_DEBUG_ASSERT(v == uint32_t(-1) || (v >> 20) == 0);
        }

        constexpr explicit operator uint32_t() const noexcept
        {
            return v_;
        }

        constexpr bool operator==(unsigned_20 const &o) const noexcept
        {
            return v_ == o.v_;
        }

        constexpr auto operator<=>(unsigned_20 const &o) const noexcept
        {
            return v_ <=> o.v_;
        }

    #define MONAD_DB_METADATA_UNSIGNED_20_STAMP(op)                            \
        template <std::integral T>                                             \
            requires(sizeof(T) <= 2)                                           \
        constexpr unsigned_20 operator op(T const &o) const noexcept           \
        {                                                                      \
            return (v_ op o) & 0xfffff;                                        \
        }                                                                      \
        template <std::integral T>                                             \
            requires(sizeof(T) > 2)                                            \
        constexpr T operator op(T const &o) const noexcept                     \
        {                                                                      \
            return (T(v_) op o);                                               \
        }                                                                      \
        constexpr unsigned_20 operator op(unsigned_20 const &o) const noexcept \
        {                                                                      \
            return (v_ op o.v_) & 0xfffff;                                     \
        }
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(+)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(-)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(&)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(|)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(^)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(>>)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(<<)
    #undef MONAD_DB_METADATA_UNSIGNED_20_STAMP

    #define MONAD_DB_METADATA_UNSIGNED_20_STAMP(op)                            \
        constexpr unsigned_20 &operator op(unsigned_20 const &o) noexcept      \
        {                                                                      \
            v_ op o.v_;                                                        \
            v_ &= 0xfffff;                                                     \
            return *this;                                                      \
        }
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(+=)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(-=)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(&=)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(|=)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(^=)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(>>=)
        MONAD_DB_METADATA_UNSIGNED_20_STAMP(<<=)
    #undef MONAD_DB_METADATA_UNSIGNED_20_STAMP
    };
#endif
}

MONAD_MPT_NAMESPACE_END
