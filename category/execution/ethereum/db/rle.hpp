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
#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

byte_string rle_encode(uint8_t const *data, size_t len);
void rle_decode(uint8_t const *in, size_t in_len, uint8_t *out, size_t out_len);

template <typename T>
    requires std::is_trivially_copyable_v<T>
T rle_decode(uint8_t const *in, size_t in_len)
{
    T result{};
    rle_decode(in, in_len, reinterpret_cast<uint8_t *>(&result), sizeof(T));
    return result;
}

MONAD_NAMESPACE_END
