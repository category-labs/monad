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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace monad::vm::evm
{
    inline constexpr std::array<uint8_t, 3> delegation_indicator_prefix_bytes{
        0xef, 0x01, 0x00};

    inline constexpr size_t delegation_indicator_size =
        delegation_indicator_prefix_bytes.size() + sizeof(Address);

    byte_string_view delegation_indicator_prefix();

    bool is_delegated(std::span<uint8_t const> code);
}
