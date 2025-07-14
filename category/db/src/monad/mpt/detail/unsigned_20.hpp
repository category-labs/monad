#pragma once

#include <monad/mpt/config.hpp>

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
