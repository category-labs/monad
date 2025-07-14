#pragma once

#include <monad/config.hpp>

#include <cstring> // for memcpy
#include <type_traits>

MONAD_NAMESPACE_BEGIN

//! \brief A constexpr-capable `memcpy`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
constexpr inline T *cmemcpy(T *const dst, const T *const src, const size_t num)
{
#if __cpp_lib_is_constant_evaluated >= 201811
    if (std::is_constant_evaluated()) {
#endif
        for (size_t n = 0; n < num; n++) {
            dst[n] = src[n];
        }
#if __cpp_lib_is_constant_evaluated >= 201811
    }
    else {
        std::memcpy(dst, src, num);
    }
#endif
    return dst;
}

//! \brief A constexpr-capable `memcmp`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
constexpr inline int
cmemcmp(const T *const a, const T *const b, const size_t num)
{
#if __cpp_lib_is_constant_evaluated >= 201811
    if (std::is_constant_evaluated()) {
#endif
        for (size_t n = 0; n < num; n++) {
            if (a[n] < b[n]) {
                return -1;
            }
            else if (a[n] > b[n]) {
                return 1;
            }
        }
        return 0;
#if __cpp_lib_is_constant_evaluated >= 201811
    }
    else {
        return std::memcmp(a, b, num);
    }
#endif
}

//! \brief A constexpr-capable `memset`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
constexpr inline T *cmemset(T *const dst, const T value, const size_t num)
{
#if __cpp_lib_is_constant_evaluated >= 201811
    if (std::is_constant_evaluated()) {
#endif
        for (size_t n = 0; n < num; n++) {
            dst[n] = value;
        }
#if __cpp_lib_is_constant_evaluated >= 201811
    }
    else {
        std::memset(dst, (int)value, num);
    }
#endif
    return dst;
}

MONAD_NAMESPACE_END
