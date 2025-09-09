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

#include <category/core/bytes.hpp>

#include <span>
#include <string_view>

#include <cthash/sha3/keccak.hpp>

MONAD_NAMESPACE_BEGIN

consteval uint32_t abi_encode_selector(std::string_view const function_name)
{
    auto const h =
        cthash::keccak_256{}.update(std::span{function_name}).final();

    // convert to big endian
    return (static_cast<uint32_t>(h[0]) << 24) |
           (static_cast<uint32_t>(h[1]) << 16) |
           (static_cast<uint32_t>(h[2]) << 8) | static_cast<uint32_t>(h[3]);
}

consteval bytes32_t
abi_encode_event_signature(std::string_view const event_name)
{
    auto const h = cthash::keccak_256{}.update(std::span{event_name}).final();
    return std::bit_cast<bytes32_t>(h);
}

MONAD_NAMESPACE_END
