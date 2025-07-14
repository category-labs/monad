#pragma once

#include <category/core/config.hpp>

#include <category/core/endian.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

class off48_t
{
    alignas(2) std::array<char, 6> a_;

public:
    constexpr off48_t()
        : a_{}
    {
    }

    constexpr off48_t(int64_t const offset)
    {
        auto const a = std::bit_cast<std::array<char, 8>>(offset);
        if constexpr (std::endian::native == std::endian::little) {
            std::copy_n(&a[0], 6, &a_[0]);
        }
        else {
            std::copy_n(&a[2], 6, &a_[0]);
        }
    }

    constexpr operator int64_t() const
    {
        std::array<char, 8> a{};
        if constexpr (std::endian::native == std::endian::little) {
            std::copy_n(&a_[0], 6, &a[0]);
        }
        else {
            std::copy_n(&a_[0], 6, &a[2]);
        }
        return std::bit_cast<int64_t>(a);
    }
};

static_assert(sizeof(off48_t) == 6);
static_assert(alignof(off48_t) == 2);

MONAD_NAMESPACE_END
