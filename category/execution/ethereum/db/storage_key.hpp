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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

#include <cstdint>
#include <cstring>
#include <optional>

MONAD_NAMESPACE_BEGIN

// Composite cache key combining domain scope, account address, account
// incarnation, and the storage trie key. The trie key is slot_key for
// slot-encoded storage or page_key for page-encoded storage; the cache layer
// is encoding-agnostic.
struct StorageKey
{
    static constexpr size_t k_domain_prefix_bytes = 1 + sizeof(uint64_t);
    static constexpr size_t k_payload_bytes =
        sizeof(Address) + sizeof(Incarnation) + sizeof(bytes32_t);
    static constexpr size_t k_bytes = k_domain_prefix_bytes + k_payload_bytes;

    uint8_t bytes[k_bytes];

    StorageKey() = default;

    StorageKey(
        Address const &addr, Incarnation const incarnation,
        bytes32_t const &key,
        std::optional<uint64_t> const &domain = std::nullopt)
    {
        bytes[0] = domain.has_value() ? uint8_t{1} : uint8_t{0};
        uint64_t const domain_value = domain.value_or(uint64_t{});
        memcpy(&bytes[1], &domain_value, sizeof(domain_value));

        constexpr size_t address_offset = k_domain_prefix_bytes;
        memcpy(&bytes[address_offset], addr.bytes, sizeof(Address));
        constexpr size_t incarnation_offset = address_offset + sizeof(Address);
        memcpy(&bytes[incarnation_offset], &incarnation, sizeof(Incarnation));
        constexpr size_t key_offset = incarnation_offset + sizeof(Incarnation);
        memcpy(&bytes[key_offset], key.bytes, sizeof(bytes32_t));
    }

    bool operator==(StorageKey const &other) const
    {
        return memcmp(bytes, other.bytes, k_bytes) == 0;
    }
};

MONAD_NAMESPACE_END
