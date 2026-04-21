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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <cstring>

MONAD_NAMESPACE_BEGIN

struct StorageKey
{
    static constexpr size_t k_bytes =
        sizeof(Address) + sizeof(Incarnation) + sizeof(bytes32_t);

    uint8_t bytes[k_bytes];

    StorageKey() = default;

    StorageKey(
        Address const &addr, Incarnation incarnation, bytes32_t const &key)
    {
        memcpy(bytes, addr.bytes, sizeof(Address));
        memcpy(&bytes[sizeof(Address)], &incarnation, sizeof(Incarnation));
        memcpy(
            &bytes[sizeof(Address) + sizeof(Incarnation)],
            key.bytes,
            sizeof(bytes32_t));
    }

    bool operator==(StorageKey const &other) const
    {
        return memcmp(bytes, other.bytes, k_bytes) == 0;
    }
};

MONAD_NAMESPACE_END
