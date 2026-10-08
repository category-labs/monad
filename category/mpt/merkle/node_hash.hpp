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

#include <category/crypto/keccak.h>
#include <category/mpt/config.hpp>

#include <blake3.h>

#include <cstddef>

MONAD_MPT_NAMESPACE_BEGIN

// 32-byte hash of a node's RLP (or of a short root), keccak256 by default
// or BLAKE3 when the build selects it. `dest` may alias `data`.
inline void node_hash(
    unsigned char const *const data, size_t const len,
    unsigned char *const dest) noexcept
{
    if constexpr (NODE_HASH_BLAKE3) {
        blake3_hasher hasher;
        blake3_hasher_init(&hasher);
        blake3_hasher_update(&hasher, data, len);
        blake3_hasher_finalize(&hasher, dest, BLAKE3_OUT_LEN);
    }
    else {
        monad_keccak256(data, len, dest);
    }
}

MONAD_MPT_NAMESPACE_END
