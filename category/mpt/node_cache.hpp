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

#include <cstdint>
#include <memory>

MONAD_MPT_NAMESPACE_BEGIN

// Memory bounded node cache
class NodeCache final
    : private static_lru_cache<
          virtual_chunk_offset_t,
          std::pair<std::shared_ptr<CacheNode>, unsigned>,
          virtual_chunk_offset_t_hasher>
{
    // second in value is node size
    using Base = static_lru_cache<
        virtual_chunk_offset_t, std::pair<std::shared_ptr<CacheNode>, unsigned>,
        virtual_chunk_offset_t_hasher>;

    size_t max_bytes_;
    size_t used_bytes_{0};

    void evict_until_under_limit()
    {
        while (used_bytes_ > max_bytes_ && !active_list_.empty()) {
            auto list_it = std::prev(active_list_.end());
            auto &node_to_erase = *list_it;
            map_.erase(list_it->key);
            used_bytes_ -= list_it->val.second;
            // move to empty list
            active_list_.erase(list_it);
            node_to_erase.key = virtual_chunk_offset_t::invalid_value();
            node_to_erase.val = {nullptr, 0};
            free_list_.push_front(node_to_erase);
        }
    }

public:
    static constexpr size_t AVERAGE_NODE_SIZE = 100;

    using Base::ConstAccessor;
    using Base::list_node;

    using Base::clear;
    using Base::find;
    using Base::size;

    explicit NodeCache(size_t const max_bytes)
        : Base(
              max_bytes / AVERAGE_NODE_SIZE,
              virtual_chunk_offset_t::invalid_value(), {nullptr, 0})
        , max_bytes_(max_bytes)
        , used_bytes_{0}
    {
    }

    ~NodeCache() = default;

    Map::iterator insert(
        virtual_chunk_offset_t const &virt_offset,
        std::shared_ptr<CacheNode> const &sp) noexcept
    {
        MONAD_ASSERT(virt_offset != virtual_chunk_offset_t::invalid_value());

        used_bytes_ += sp->get_mem_size();
        evict_until_under_limit();

        auto const [it, erased_value] =
            Base::insert(virt_offset, {sp, sp->get_mem_size()});
        if (erased_value.has_value()) {
            used_bytes_ -= erased_value->second;
        }
        return it;
    }
};

MONAD_MPT_NAMESPACE_END
