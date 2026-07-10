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
#include <category/core/config.hpp>

#include <cstdint>
#include <cstring>
#include <optional>

MONAD_NAMESPACE_BEGIN

// Composite cache key combining namespace scope and account address.
struct AccountKey
{
    static constexpr size_t k_namespace_prefix_bytes = 1 + sizeof(uint64_t);
    static constexpr size_t k_payload_bytes = sizeof(Address);
    static constexpr size_t k_bytes =
        k_namespace_prefix_bytes + k_payload_bytes;

    uint8_t bytes[k_bytes];

    AccountKey() = default;

    explicit AccountKey(Address const &addr, std::optional<uint64_t> const &ns)
    {
        bytes[0] = ns.has_value() ? uint8_t{1} : uint8_t{0};
        uint64_t const ns_value = ns.value_or(uint64_t{});
        memcpy(&bytes[1], &ns_value, sizeof(ns_value));

        constexpr size_t address_offset = k_namespace_prefix_bytes;
        memcpy(&bytes[address_offset], addr.bytes, sizeof(Address));
    }

    bool operator==(AccountKey const &other) const
    {
        return memcmp(bytes, other.bytes, k_bytes) == 0;
    }
};

MONAD_NAMESPACE_END
