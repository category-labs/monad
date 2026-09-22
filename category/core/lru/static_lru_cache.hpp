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
#include <category/core/config.hpp>
#include <category/core/lru/cache_stats.hpp>

#include <boost/intrusive/list.hpp>

#include <ankerl/unordered_dense.h>

#include <atomic>
#include <cstddef>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

// An LRU cache with a fixed max size. Calls to `find()` will not allocate.
template <
    typename Key, typename Value,
    typename Hash = ankerl::unordered_dense::hash<Key>>
class static_lru_cache
{
public:
    struct list_node
        : public boost::intrusive::list_base_hook<
              boost::intrusive::link_mode<boost::intrusive::normal_link>>
    {
        Key key;
        Value val;
    };

protected:
    using List = boost::intrusive::list<list_node>;
    using ListIter = typename List::iterator;
    using Map = ankerl::unordered_dense::segmented_map<Key, ListIter, Hash>;

private:
    std::vector<list_node> array_;
    boost::intrusive::list<list_node> active_list_;
    boost::intrusive::list<list_node> free_list_;
    Map map_;
    // evictions counts this class's slot bound and any derived class's bound
    // together; the total cannot attribute either.
    CacheStats stats_;
    // Mirrors map_.size(); every path that changes map_ membership must call
    // publish_size().
    std::atomic<size_t> size_{0};

public:
    using ConstAccessor = Map::const_iterator;

    explicit static_lru_cache(
        size_t const size, Key const &key = Key(), Value const &value = Value())
        : array_(size, list_node{.key = key, .val = value})
    {
        MONAD_ASSERT(size != 0);
        for (size_t i = 0; i < size; ++i) {
            free_list_.push_back(array_[i]);
        }
        map_.reserve(size);

        MONAD_ASSERT(free_list_.size() == array_.size());
        MONAD_ASSERT(active_list_.size() == 0);
    }

    ~static_lru_cache() = default;

    // return the map iterator and the erased value if any
    std::pair<typename Map::iterator, std::optional<Value>>
    insert(Key const &key, Value const &value) noexcept
    {
        MONAD_DEBUG_ASSERT(
            size_.load(std::memory_order_relaxed) == map_.size());
        std::optional<Value> erased_value = std::nullopt;
        if (auto const it = map_.find(key); it != map_.end()) {
            erased_value = it->second->val;
            it->second->val = value;
            update_lru(it->second);
            return {it, erased_value};
        }
        if (free_list_.empty()) {
            erased_value = evict_lru_tail();
        }
        auto const free_it = free_list_.begin();
        list_node *const node = &*free_it;
        free_list_.erase(free_it);

        node->key = key;
        node->val = value;

        active_list_.insert(active_list_.begin(), *node);
        auto const it =
            map_.emplace(key, active_list_.iterator_to(*node)).first;
        publish_size();
        return {it, erased_value};
    }

    // Counts as a lookup. Use contains() for a predicate, or the hit rate
    // moves for a read nobody made.
    bool find(ConstAccessor &acc, Key const &key) noexcept
    {
        acc = map_.find(key);
        if (acc == map_.end()) {
            stats_.record_miss();
            return false;
        }
        stats_.record_hit();
        update_lru(acc->second);
        return true;
    }

    // Existence check that records no hit or miss and leaves the LRU order
    // alone. Owning thread only, like find(): it reads the map.
    bool contains(Key const &key) const noexcept
    {
        return map_.find(key) != map_.end();
    }

    size_t size() const noexcept
    {
        return size_.load(std::memory_order_relaxed);
    }

    CacheStatsSnapshot stats() const noexcept
    {
        return stats_.snapshot();
    }

    // Empties the index and returns every node to the free list. A node left
    // on the active list is reused by the next insert and counted as an
    // eviction, so both halves matter. Leaves the counters alone.
    void clear() noexcept
    {
        MONAD_DEBUG_ASSERT(
            size_.load(std::memory_order_relaxed) == map_.size());
        while (!active_list_.empty()) {
            recycle_lru_tail();
        }
    }

protected:
    // Drops the LRU tail and counts it. The one place a derived cache
    // evicting on its own bound should call, so it cannot leave half the
    // bookkeeping behind.
    Value evict_lru_tail() noexcept
    {
        stats_.record_eviction();
        return recycle_lru_tail();
    }

private:
    // Removes the LRU tail from the index and the active list, returns the
    // node to the free list, and returns its value. Uncounted, because
    // clear() removes entries without evicting them.
    Value recycle_lru_tail() noexcept
    {
        MONAD_DEBUG_ASSERT(!active_list_.empty());
        auto const list_it = std::prev(active_list_.end());
        auto &node = *list_it;
        Value removed = node.val;
        map_.erase(node.key);
        active_list_.erase(list_it);
        // The key is left alone: nothing reads a free-list node's key, and
        // resetting it would require Key to be default-constructible, which
        // virtual_chunk_offset_t is not.
        node.val = Value();
        free_list_.push_back(node);
        publish_size();
        return removed;
    }

    void publish_size() noexcept
    {
        size_.store(map_.size(), std::memory_order_relaxed);
    }

    void update_lru(ListIter const it)
    {
        active_list_.splice(active_list_.begin(), active_list_, it);
    }
};

MONAD_NAMESPACE_END
