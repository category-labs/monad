// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/seeded_fast_hash.hpp>

#include <category/core/config.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#include <komihash.h>
#pragma GCC diagnostic pop

#include <cstddef>
#include <cstdint>
#include <mutex>
#include <random>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

uint64_t g_seed = 143;

std::once_flag g_seed_once;

uint64_t hash_seed() noexcept
{
    static uint64_t const seed = g_seed;
    return seed;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

uint64_t set_hash_seed()
{
    std::call_once(g_seed_once, [] {
        std::random_device rd;
        g_seed = std::uniform_int_distribution<uint64_t>{}(rd);
    });
    return hash_seed();
}

uint64_t seeded_fast_hash(void const *const data, size_t const len) noexcept
{
    return komihash(data, len, hash_seed());
}

MONAD_NAMESPACE_END
