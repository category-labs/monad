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
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <tbb/concurrent_hash_map.h>

MONAD_NAMESPACE_BEGIN

class PageStorageBroker final
{
public:
    using PageKey = StorageKey;
    using PageKeyHashCompare = BytesHashCompare<PageKey>;
    using PageMap =
        tbb::concurrent_hash_map<PageKey, storage_page_t, PageKeyHashCompare>;

    size_t page_count() const
    {
        return pages_.size();
    }

    Db &db()
    {
        return db_;
    }

    explicit PageStorageBroker(Db &db)
        : db_{db}
    {
    }

    bytes32_t read_storage_slot(
        Address const &addr, Incarnation const inc, bytes32_t const &key)
    {
        auto const page_key = compute_page_key(key);
        auto const slot_offset = compute_slot_offset(key);
        PageKey const pk{addr, inc, page_key};

        {
            PageMap::const_accessor acc;
            if (pages_.find(acc, pk)) {
                return acc->second[slot_offset];
            }
        }

        // Load without holding any tbb accessor: db_.read_storage yields
        // the fiber waiting on an mpt promise. Holding a tbb bucket lock
        // across that yield deadlocks against other fibers that need the
        // same bucket - tbb's spin/futex isn't fiber-aware, so the OS
        // thread blocks and the fiber dispatcher can't make progress.
        // Two fibers may load the same page; only the first insert keeps
        // its result, the rest is wasted work but safe.
        auto loaded = load_page(addr, inc, page_key);

        PageMap::accessor acc;
        if (pages_.insert(acc, pk)) {
            acc->second = std::move(loaded);
        }
        return acc->second[slot_offset];
    }

    storage_page_t read_storage_page(
        Address const &addr, Incarnation const inc, bytes32_t const &page_key)
    {
        PageKey const pk{addr, inc, page_key};

        {
            PageMap::const_accessor acc;
            if (pages_.find(acc, pk)) {
                return acc->second;
            }
        }

        // See read_storage_slot: load outside the accessor to avoid a
        // tbb-vs-fiber deadlock when db_.read_storage yields.
        auto loaded = load_page(addr, inc, page_key);

        PageMap::accessor acc;
        if (pages_.insert(acc, pk)) {
            acc->second = std::move(loaded);
        }
        return acc->second;
    }

private:
    Db &db_;
    PageMap pages_;

    storage_page_t load_page(
        Address const &addr, Incarnation const inc, bytes32_t const &page_key)
    {
        auto const raw = db_.read_storage(addr, inc, page_key);
        if (raw.empty()) {
            return storage_page_t{};
        }
        auto res = decode_storage_page(raw);
        MONAD_ASSERT(res.has_value());
        return res.value();
    }
};

MONAD_NAMESPACE_END
