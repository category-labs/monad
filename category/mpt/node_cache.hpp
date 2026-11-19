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

#include <category/core/lru/static_lru_cache.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/util.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>

MONAD_MPT_NAMESPACE_BEGIN

// Memory bounded node cache
class NodeCache final
    : private static_lru_cache<
          virtual_chunk_offset_t, std::pair<std::shared_ptr<Node>, unsigned>,
          virtual_chunk_offset_t_hasher>
{
    // second in value is node size
    using Base = static_lru_cache<
        virtual_chunk_offset_t, std::pair<std::shared_ptr<Node>, unsigned>,
        virtual_chunk_offset_t_hasher>;

    size_t max_bytes_;

    void evict_until_under_limit(size_t used)
    {
        while (used > max_bytes_ && size() != 0) {
            used -= evict_lru_tail().second;
        }
        // An empty cache owes no bytes. A nonzero balance here means the
        // accounting has drifted, and since eviction clamps it back to
        // max_bytes_ on the way down, every later insert over-evicts until
        // the cache holds nothing at all.
        MONAD_DEBUG_ASSERT(size() != 0 || used == 0);
        publish_occupancy(used);
    }

public:
    static constexpr size_t AVERAGE_NODE_SIZE = 104;

    using Base::ConstAccessor;
    using Base::list_node;

    using Base::contains;
    using Base::find;
    using Base::size;
    using Base::stats;
    using Base::stats_handle;

    // Private inheritance already puts Base::clear out of reach; this states
    // the intent at the point someone would try to re-export it. Clearing
    // without also zeroing the byte total would leave a full balance over an
    // empty map, and the next insert would evict everything forever.
    void clear() = delete;

    // Sum of get_mem_size() over cached nodes; bounded by max_bytes().
    [[nodiscard]] size_t used_bytes() const noexcept
    {
        return Base::published_used_bytes();
    }

    [[nodiscard]] size_t max_bytes() const noexcept
    {
        return max_bytes_;
    }

    explicit NodeCache(size_t const max_bytes)
        : Base(
              max_bytes / AVERAGE_NODE_SIZE,
              virtual_chunk_offset_t::invalid_value(), {nullptr, 0})
        , max_bytes_(max_bytes)
    {
        MONAD_ASSERT_PRINTF(
            max_bytes >= AVERAGE_NODE_SIZE,
            "node cache budget %zu is below one average node (%zu); it would "
            "have no slots",
            max_bytes,
            AVERAGE_NODE_SIZE);
        publish_byte_capacity(max_bytes);
    }

    ~NodeCache() = default;

    void insert(
        virtual_chunk_offset_t const &virt_offset,
        std::shared_ptr<Node> const &sp) noexcept
    {
        MONAD_ASSERT(virt_offset != virtual_chunk_offset_t::invalid_value());
        MONAD_ASSERT(sp != nullptr);

        auto const node_bytes = sp->get_mem_size();
        // Caching it would evict every other entry and then itself, emptying
        // a healthy cache to store nothing.
        if (node_bytes > max_bytes_) {
            return;
        }

        // Both levels change, so publish them together at the end.
        defer_occupancy();
        auto const [_, erased_value] =
            Base::insert(virt_offset, {sp, node_bytes});
        // erased_value is set either by an overwrite of this same key or by
        // the slot-bound eviction Base::insert just did; either way those
        // bytes have left, so charging the net keeps the published byte total
        // equal to the sum of what is stored.
        auto used = used_bytes() + node_bytes;
        if (erased_value.has_value()) {
            used -= erased_value->second;
        }
        evict_until_under_limit(used);
    }
};

MONAD_MPT_NAMESPACE_END
