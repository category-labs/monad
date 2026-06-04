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

// Shared zkVM shadow of category/core/keccak.hpp. Mirrors the host header's
// public surface (the global ::keccak256, the monad::hash256 alias, and the
// byte_string_view overload) but defines hash256 locally instead of pulling
// it from <ethash/hash_types.hpp>, since the zkVM build doesn't depend on
// ethash. The underlying ::keccak256 comes from the per-zkVM accelerator
// (see zkvm/category/core/keccak.h).

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/keccak.h>

#include <cstddef>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

using ::keccak256;

// 32-byte hash type. Field name matches ethash::hash256 (`bytes`) so
// existing call sites (e.g. `hash.bytes`) work unchanged.
struct hash256
{
    std::uint8_t bytes[KECCAK256_SIZE];
};

inline hash256 keccak256(byte_string_view const bytes)
{
    hash256 hash{};
    keccak256(bytes.data(), bytes.size(), hash.bytes);
    return hash;
}

template <std::size_t N>
inline hash256 keccak256(unsigned char const (&a)[N])
{
    return keccak256(to_byte_string_view(a));
}

MONAD_NAMESPACE_END
