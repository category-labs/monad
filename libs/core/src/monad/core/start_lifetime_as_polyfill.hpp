#pragma once

#include "../config.hpp"

#ifndef MONAD_USE_STD_START_LIFETIME_AS
    #if __cpp_lib_start_lifetime_as >= 202207L
        #define MONAD_USE_STD_START_LIFETIME_AS 1
    #else
        #define MONAD_USE_STD_START_LIFETIME_AS 0
    #endif
#endif

#if MONAD_USE_STD_START_LIFETIME_AS
    #include <memory>
#endif

namespace monad
{
#if MONAD_USE_STD_START_LIFETIME_AS
    using std::start_lifetime_as;
    using std::start_lifetime_as_array;
#else
    template <class T>
    inline T *start_lifetime_as(void *p) noexcept
    {
        return reinterpret_cast<T *>(p);
    }

    template <class T>
    inline T const *start_lifetime_as(void const *p) noexcept
    {
        return reinterpret_cast<T const *>(p);
    }

    template <class T>
    inline T volatile *start_lifetime_as(void volatile *p) noexcept
    {
        return reinterpret_cast<T volatile *>(p);
    }

    template <class T>
    inline T const volatile *start_lifetime_as(void const volatile *p) noexcept
    {
        return reinterpret_cast<T const volatile *>(p);
    }

    template <class T>
    inline T *start_lifetime_as_array(void *p, std::size_t) noexcept
    {
        return reinterpret_cast<T *>(p);
    }

    template <class T>
    inline T const *start_lifetime_as_array(void const *p, std::size_t) noexcept
    {
        return reinterpret_cast<T const *>(p);
    }

    template <class T>
    inline T volatile *
    start_lifetime_as_array(void volatile *p, std::size_t) noexcept
    {
        return reinterpret_cast<T volatile *>(p);
    }

    template <class T>
    inline T const volatile *
    start_lifetime_as_array(void const volatile *p, std::size_t) noexcept
    {
        return reinterpret_cast<T const volatile *>(p);
    }
#endif
}
