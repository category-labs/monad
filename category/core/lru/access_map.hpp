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

#include <ankerl/unordered_dense.h>

#include <atomic>
#include <chrono>
#include <mutex>
#include <string>

MONAD_NAMESPACE_BEGIN

template <typename Key, typename Hash = ankerl::unordered_dense::hash<Key>>
class AccessMap
{
    size_t max_size_{0};
    size_t size_{0};

    using Map = ankerl::unordered_dense::segmented_map<Key, uint64_t, Hash>;
    std::deque<std::pair<uint64_t, std::vector<Key>>> access_log_;
    Map last_access_map_;

public:
    explicit AccessMap(size_t const max_size)
        : max_size_(max_size)
        , size_(0)
    {
    }

    AccessMap(AccessMap const &) = delete;
    AccessMap &operator=(AccessMap const &) = delete;

    void init_new_block(uint64_t const block_number)
    {
        access_log_.emplace_back(block_number, std::vector<Key>{});
    }

    // Returns the oldest block number still in the access log after
    // finalize or std::nullopt if access logs empty (rarely happens)
    std::optional<uint64_t> finish_insert()
    {
        while (size_ > max_size_) {
            auto const &oldest = access_log_.front();
            for (auto const &key : oldest.second) {
                auto const it = last_access_map_.find(key);
                MONAD_ASSERT(it != last_access_map_.end());
                if (it->second == oldest.first) {
                    last_access_map_.erase(it);
                }
            }
            size_ -= oldest.second.size();
            access_log_.pop_front();
        }
        return access_log_.empty()
                   ? std::nullopt
                   : std::optional<uint64_t>(access_log_.front().first);
    }

    void insert(Key const &key)
    {
        MONAD_ASSERT(access_log_.size());
        last_access_map_[key] = access_log_.back().first;
        access_log_.back().second.push_back(key);
        ++size_;
    }

    bool contains(Key const &key) const
    {
        return last_access_map_.contains(key);
    }

    std::optional<uint64_t> get_last_access_block(Key const &key) const
    {
        auto const it = last_access_map_.find(key);
        if (it == last_access_map_.end()) {
            return std::nullopt;
        }
        return it->second;
    }
};

MONAD_NAMESPACE_END
