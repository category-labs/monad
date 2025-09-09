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

#include <cthash/sha3/common.hpp>

// cthash only provides sha3 and not keccak. this function modifies the suffix
// in the trait to return keccaked values
namespace cthash
{
    struct keccak_config
    {
        static constexpr size_t digest_length_bit = 256u;
        static constexpr size_t capacity_bit = 512u;
        static constexpr size_t rate_bit = 1600u - capacity_bit;

        // Note that the library uses this trait internally as such:
        //
        // constexpr std::byte suffix_and_start_of_padding =
        //      (suffix.values[0] | (std::byte{0b0000'0001u} << suffix.bits));
        //
        // So this yields domain bit = 0x01
        static constexpr auto suffix = keccak_suffix(0, 0x00);
    };

    static_assert(
        keccak_config::rate_bit + keccak_config::capacity_bit == 1600u);

    using keccak_256 = keccak_hasher<keccak_config>;
}

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
