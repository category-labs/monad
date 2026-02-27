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
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/page_storage_cache.hpp>
#include <category/execution/ethereum/db/storage_page.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

#include <tbb/concurrent_hash_map.h>

#include <cstring>

MONAD_NAMESPACE_BEGIN

template <
    size_t SlotBits = storage_page_t::MONAD_SLOT_BITS,
    uint8_t SlotMask = storage_page_t::MONAD_SLOT_MASK>
class MonadPageStorageCache final : public PageStorageCache
{
public:
    struct PageKey
    {
        static constexpr size_t k_bytes =
            sizeof(Address) + sizeof(Incarnation) + sizeof(bytes32_t);

        uint8_t bytes[k_bytes];

        PageKey() = default;

        PageKey(
            Address const &addr, Incarnation incarnation,
            bytes32_t const &page_key)
        {
            memcpy(bytes, addr.bytes, sizeof(Address));
            memcpy(&bytes[sizeof(Address)], &incarnation, sizeof(Incarnation));
            memcpy(
                &bytes[sizeof(Address) + sizeof(Incarnation)],
                page_key.bytes,
                sizeof(bytes32_t));
        }
    };

    using PageKeyHashCompare = BytesHashCompare<PageKey>;
    using PageMap =
        tbb::concurrent_hash_map<PageKey, storage_page_t, PageKeyHashCompare>;

    PageMap &pages()
    {
        return pages_;
    }

private:
    Db &db_;
    PageMap pages_;

public:
    explicit MonadPageStorageCache(Db &db)
        : db_{db}
    {
    }

    Db &db() override
    {
        return db_;
    }

    bytes32_t read_storage(
        Address const &addr, Incarnation inc, bytes32_t const &key) override
    {
        bytes32_t const page_key = compute_page_key<SlotBits>(key);
        uint8_t const slot_offset = compute_slot_offset<SlotMask>(key);

        PageKey const pk{addr, inc, page_key};

        {
            typename PageMap::const_accessor acc;
            if (pages_.find(acc, pk)) {
                return acc->second[slot_offset];
            }
        }

        typename PageMap::accessor acc;
        if (pages_.insert(acc, pk)) {
            acc->second = decode_storage_value<storage_page_t>(
                db_.read_storage(addr, inc, page_key));
        }
        return acc->second[slot_offset];
    }

    storage_page_t read_storage_page(
        Address const &addr, Incarnation inc,
        bytes32_t const &page_key) override
    {
        PageKey const pk{addr, inc, page_key};

        {
            typename PageMap::const_accessor acc;
            if (pages_.find(acc, pk)) {
                return acc->second;
            }
        }

        typename PageMap::accessor acc;
        if (pages_.insert(acc, pk)) {
            acc->second = decode_storage_value<storage_page_t>(
                db_.read_storage(addr, inc, page_key));
        }
        return acc->second;
    }
};

MONAD_NAMESPACE_END
