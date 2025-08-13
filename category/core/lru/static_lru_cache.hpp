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

#include <category/core/config.hpp>
#include <category/core/unordered_map.hpp>

#include <boost/intrusive/list.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

// An LRU cache with a fixed max size. Calls to `find()` will not allocate.
template <
    typename Key, typename Value,
    typename Hash = ankerl::unordered_dense::hash<Key>>
class static_lru_cache
{
    struct list_node
        : public boost::intrusive::list_base_hook<
              boost::intrusive::link_mode<boost::intrusive::normal_link>>
    {
        Key key;
        Value val;
    };

    using List = boost::intrusive::list<list_node>;
    using ListIter = typename List::iterator;
    using Map = ankerl::unordered_dense::segmented_map<Key, ListIter, Hash>;

    std::vector<list_node> array_;
    boost::intrusive::list<list_node> list_;
    Map map_;

public:
    using ConstAccessor = Map::const_iterator;

    explicit static_lru_cache(
        size_t const size, Key const &key = Key(), Value const &value = Value())
        : array_(size, list_node{.key = key, .val = value})
    {
        for (size_t i = 0; i < size; ++i) {
            list_.push_back(array_[i]);
        }
        map_.reserve(size);
    }

    ~static_lru_cache() = default;

    void insert(Key const &key, Value const &value) noexcept
    {
        auto it = map_.find(key);
        if (it != map_.end()) {
            it->second->val = value;
            update_lru(it->second);
        }
        else {
            auto it = std::prev(list_.end());
            map_.erase(it->key);
            list_.erase(it);

            // Reuse node
            it->key = key;
            it->val = value;

            list_.insert(list_.begin(), *it);
            map_[key] = it;
        }
    }

    bool find(ConstAccessor &acc, Key const &key) noexcept
    {
        acc = map_.find(key);
        if (acc == map_.end()) {
            return false;
        }
        update_lru(acc->second);
        return true;
    }

    size_t size() const noexcept
    {
        return map_.size();
    }

    void clear() noexcept
    {
        map_.clear();
    }

private:
    void update_lru(ListIter it)
    {
        list_.splice(list_.begin(), list_, it);
    }
};

MONAD_NAMESPACE_END
