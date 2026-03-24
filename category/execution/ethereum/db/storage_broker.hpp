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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/storage_encoding.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

MONAD_NAMESPACE_BEGIN

struct StorageBroker
{
    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) = 0;

    virtual ~StorageBroker() = default;
};

class SlotStorageBroker final : public StorageBroker
{
    Db &db_;

public:
    explicit SlotStorageBroker(Db &db)
        : db_{db}
    {
    }

    bytes32_t read_storage(
        Address const &addr, Incarnation inc, bytes32_t const &key) override
    {
        return decode_storage_eth(db_.read_storage(addr, inc, key));
    }
};

MONAD_NAMESPACE_END
