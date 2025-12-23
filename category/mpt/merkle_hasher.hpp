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

#include <category/core/keccak.h>
#include <category/mpt/config.hpp>

#include <concepts>
#include <cstddef>

MONAD_MPT_NAMESPACE_BEGIN

// Hash output size for all merkle hasher traits
inline constexpr unsigned HASH_SIZE = 32;

template <typename T>
concept MerkleHasher =
    requires(unsigned char const *in, size_t len, unsigned char *out) {
        { T::hash(in, len, out) } -> std::same_as<void>;
    };

struct Keccak256Hasher
{
    static_assert(KECCAK256_SIZE == HASH_SIZE);

    static void hash(unsigned char const *in, size_t len, unsigned char *out)
    {
        keccak256(in, static_cast<unsigned long>(len), out);
    }
};

MONAD_MPT_NAMESPACE_END
