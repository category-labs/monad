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

#include <category/core/config.hpp>
#include <category/core/byte_string.hpp>

#include <blake3.h>
#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

using hash256 = ethash::hash256;

inline hash256 blake3(byte_string_view const bytes)
{
    hash256 hash;
    static_assert(sizeof(hash256) == BLAKE3_OUT_LEN);

    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    blake3_hasher_update(&hasher, bytes.data(), bytes.size());
    blake3_hasher_finalize(&hasher, hash.bytes, BLAKE3_OUT_LEN);
    return hash;
}

MONAD_NAMESPACE_END
