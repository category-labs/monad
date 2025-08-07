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
 * Primitive Ethereum vocabulary types that cross C ABI boundaries. These types
 * have a well-defined C layout for the sake of cross-language interoperability,
 * but when hosted in a C++ program behave as type aliases to layout-compatible
 * types with richer interfaces, e.g., intx::uint256. The latter occurs only if
 * the headers are available, otherwise we'll get C structures with appropriate
 * size and alignment.
 */

// clang-format off

#ifdef __cplusplus

/*
 * C++ definitions
 */

#include <array>
#include <cstdint>
#include <cstring>

#if __has_include(<evmc/evmc.hpp>)
    #include <evmc/evmc.hpp>
    using monad_c_address = evmc::address;
    using monad_c_bytes32 = evmc::bytes32;
#elif __has_include(<evmc/evmc.h>)
    #include <evmc/evmc.h>
    using monad_c_address = evmc_address;
    using monad_c_bytes32 = evmc_bytes32;
#else
    using monad_c_address = std::array<std::uint8_t, 20>;
    using monad_c_bytes32 = std::array<std::uint8_t, 32>;
#endif

#if __has_include(<intx/intx.hpp>)
    #include <intx/intx.hpp>
    using monad_c_uint256_ne = intx::uint256;
#else
    // See comment in the C version of this below
    struct monad_exec_uint256_ne
    {
        std::uint64_t limbs[4];

        monad_exec_uint256_ne &operator=(monad_c_bytes32 const &rhs)
        {
            std::memcpy(this, &rhs, sizeof *this);
            return *this;
        }
    };
#endif // __has_include(<intx/intx.hpp>)

using monad_c_b64 = std::array<std::uint8_t, 8>;
using monad_c_bloom256 = std::array<std::uint8_t, 256>;

#else // #ifdef __cplusplus

/*
 * C definitions
 */

#include <stdint.h>

typedef struct monad_c_b64
{
    uint8_t bytes[8];
} monad_c_b64;

#if __has_include(<evmc/evmc.h>)
    #include <evmc/evmc.h>
    typedef evmc_address monad_c_address;
    typedef evmc_bytes32 monad_c_bytes32;
#else // __has_include(<evmc/evmc.h>)
    typedef struct monad_c_address
    {
        uint8_t bytes[20];
    } monad_c_address;

    typedef struct monad_c_bytes32
    {
        uint8_t bytes[32];
    } monad_c_bytes32;
#endif // __has_include(<evmc/evmc.h>)

// 256-bit integer stored in native endian byte order; the rationale for the
// storage layout as `uint64_t[4]` instead of `uint8_t[32]` is that this ensures
// the type is suitably-aligned to unsafely cast the underlying bits into a type
// in an extended-precision integer library, if that library internally uses a
// uint64_t[4] "limbs"-style representation. Both the C++ intx library and
// Rust's ruint package use this representation.
typedef struct monad_c_uint256_ne
{
    uint64_t limbs[4];
} monad_c_uint256_ne;

typedef struct monad_c_bloom256
{
    uint8_t bytes[256];
} monad_c_bloom256;

// clang-format on

#endif // #ifdef __cplusplus
