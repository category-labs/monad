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
    inline const T *start_lifetime_as(const void *p) noexcept
    {
        return reinterpret_cast<const T *>(p);
    }

    template <class T>
    inline volatile T *start_lifetime_as(volatile void *p) noexcept
    {
        return reinterpret_cast<volatile T *>(p);
    }

    template <class T>
    inline const volatile T *start_lifetime_as(const volatile void *p) noexcept
    {
        return reinterpret_cast<const volatile T *>(p);
    }

    template <class T>
    inline T *start_lifetime_as_array(void *p, std::size_t) noexcept
    {
        return reinterpret_cast<T *>(p);
    }

    template <class T>
    inline const T *start_lifetime_as_array(const void *p, std::size_t) noexcept
    {
        return reinterpret_cast<const T *>(p);
    }

    template <class T>
    inline volatile T *
    start_lifetime_as_array(volatile void *p, std::size_t) noexcept
    {
        return reinterpret_cast<volatile T *>(p);
    }

    template <class T>
    inline const volatile T *
    start_lifetime_as_array(const volatile void *p, std::size_t) noexcept
    {
        return reinterpret_cast<const volatile T *>(p);
    }
#endif
}
