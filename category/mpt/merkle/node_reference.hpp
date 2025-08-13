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
#include <category/core/keccak.h>
#include <category/mpt/config.hpp>
#include <category/core/rlp/encode.hpp>

#include <cstdint>
#include <cstring>

MONAD_MPT_NAMESPACE_BEGIN

// return length of noderef
inline unsigned
to_node_reference(byte_string_view rlp, unsigned char *dest) noexcept
{
    if (MONAD_LIKELY(rlp.size() >= KECCAK256_SIZE)) {
        keccak256(rlp.data(), rlp.size(), dest);
        return KECCAK256_SIZE;
    }
    else {
        std::memcpy(dest, rlp.data(), rlp.size());
        return static_cast<unsigned>(rlp.size());
    }
}

MONAD_MPT_NAMESPACE_END
