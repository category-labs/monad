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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>

#pragma once

MONAD_NAMESPACE_BEGIN

struct Address;
struct bytes32_t;
struct uint256_t;

size_t value_size(size_t);
size_t value_size(uint256_t const &);

size_t value_size(Address const &);
size_t value_size(bytes32_t const &);
size_t value_size(byte_string_view const &);
size_t value_size(byte_string const &);
size_t value_size(byte_string_fixed<8> const &);
size_t value_size(byte_string_fixed<256> const &);

size_t value_size(std::optional<Address> const &);
size_t value_size(std::optional<bytes32_t> const &);
size_t value_size(std::optional<uint64_t> const &);
size_t value_size(std::optional<uint256_t> const &);

MONAD_NAMESPACE_END
