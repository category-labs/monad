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

#include <category/core/byte_string.hpp>
#include <category/core/rlp/encode.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/merkle_hasher.hpp>

#include <cstdint>
#include <cstring>

MONAD_MPT_NAMESPACE_BEGIN

// Stores the content of `rlp` in a buffer `dest`. `dest` is at most 32 bytes.
// If the data is less than 32 bytes, it is copied into buf, otherwise it is
// hashed.
template <MerkleHasher Hasher>
inline unsigned
to_node_reference(byte_string_view const rlp, unsigned char *dest) noexcept
{
    if (MONAD_LIKELY(rlp.size() >= HASH_SIZE)) {
        Hasher::hash(rlp.data(), rlp.size(), dest);
        return HASH_SIZE;
    }
    else {
        std::memcpy(dest, rlp.data(), rlp.size());
        return static_cast<unsigned>(rlp.size());
    }
}

MONAD_MPT_NAMESPACE_END
