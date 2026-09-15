// Copyright (C) 2026 Category Labs, Inc.
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

#include <algorithm>
#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <cstdint>
#include <mutex>
#include <tbb/concurrent_hash_map.h>

MONAD_NAMESPACE_BEGIN

// One map and one intrusive eviction list. Valued entries precede the
// boundary, empty entries follow it. Admissions and renewals move to the
// front; re-entry can restore an older stamp. Unstamped values sit just
// before the boundary. Eviction skips protected values. Reads never move
// entries and no wall-clock timestamp is stored in this protocol cache.
// Map accessors protect values/stamps; the mutex protects links and totals.
template <class Key, class Value, class Hash>
class StampCache
{
    struct Links
    {
        Links *prev{nullptr}, *next{nullptr};
        Key const *key{nullptr};
    };

    struct Entry : Links
    {
        Value value_;
        uint64_t stamp{0};
        uint32_t weight{0};
        bool negative{true};
    };

    using Map = tbb::concurrent_hash_map<Key, Entry, Hash>;
    Map map_;
    mutable std::mutex mutex_;
    Links head_, boundary_, tail_;
    uint64_t const max_weight_;
    size_t const max_entries_, max_negatives_;
    uint64_t weight_{0}, floor_{1};
    size_t negatives_{0}, entries_{0};

    static void unlink(Links *node)
    {
        node->prev->next = node->next;
        node->next->prev = node->prev;
        node->prev = nullptr;
    }

    static void after(Links *pos, Links *node)
    {
        node->prev = pos;
        node->next = pos->next;
        pos->next->prev = node;
        pos->next = node;
    }

    void reset_links()
    {
        head_.next = &boundary_;
        boundary_.prev = &head_;
        boundary_.next = &tail_;
        tail_.prev = &boundary_;
    }

    Links *victim()
    {
        if (negatives_ > max_negatives_ || entries_ > max_entries_) {
            if (tail_.prev != &boundary_) {
                return tail_.prev;
            }
        }
        if (weight_ > max_weight_ || entries_ > max_entries_) {
            // Re-entry can restore an older stamp at the front. Skip
            // protected values rather than assuming stamp order in the LRU.
            for (auto *node = boundary_.prev; node != &head_; node = node->prev) {
                if (static_cast<Entry *>(node)->stamp < floor_) {
                    return node;
                }
            }
            MONAD_ASSERT_PRINTF(false,
                "eligible cache values exceed software capacity");
        }
        return nullptr;
    }

    void trim()
    {
        for (;;) {
            Key key;
            Links *target;
            {
                std::lock_guard lock{mutex_};
                target = victim();
                if (!target) {
                    return;
                }
                key = *target->key;
            }
            typename Map::accessor acc;
            if (!map_.find(acc, key)) {
                continue;
            }
            {
                std::lock_guard lock{mutex_};
                if (static_cast<Links *>(&acc->second) != target ||
                    victim() != target) {
                    continue;
                }
                auto &entry = acc->second;
                MONAD_ASSERT_PRINTF(
                    entry.stamp < floor_,
                    "eligible cache values exceed software capacity");
                unlink(&entry);
                if (entry.negative) {
                    --negatives_;
                }
                else {
                    weight_ -= entry.weight;
                }
                --entries_;
            }
            map_.erase(acc);
        }
    }

public:
    using ConstAccessor = typename Map::const_accessor;

    StampCache(uint64_t weight, size_t entries, size_t negatives)
        : max_weight_{weight}
        , max_entries_{entries}
        , max_negatives_{negatives}
    {
        reset_links();
    }

    bool find(ConstAccessor &acc, Key const &key) const
    {
        return map_.find(acc, key);
    }

    uint64_t stamp_of(ConstAccessor const &acc) const
    {
        return acc->second.stamp;
    }

    bool is_negative(ConstAccessor const &acc) const
    {
        return acc->second.negative;
    }

    void set_evict_floor(uint64_t floor)
    {
        std::lock_guard lock{mutex_};
        floor_ = floor;
    }

    // Expired values retain their stamp and position; the floor makes them
    // evictable independently of the key-history index.
    void clear_stamp(Key const &key)
    {
        typename Map::accessor acc;
        if (!map_.find(acc, key)) {
            return;
        }
        std::lock_guard lock{mutex_};
        auto &entry = acc->second;
        entry.stamp = 0;
        unlink(&entry);
        after(entry.negative ? &boundary_ : boundary_.prev, &entry);
    }

    void insert(
        Key const &key, Value const &value, uint32_t weight, bool negative,
        uint64_t stamp = 0)
    {
        typename Map::accessor acc;
        bool const added = map_.insert(acc, key);
        auto &entry = acc->second;
        // Copy then swap compacts storage buffers after shrink.
        Value copy = value;
        using std::swap;
        swap(entry.value_, copy);
        // Copies compact a page that previously grew and then shrank.
        // Charge its resident allocation, not the source buffer's capacity.
        uint32_t const stored_weight = [&] {
            if constexpr (requires { entry.value_.byte_size(); }) {
                return static_cast<uint32_t>(entry.value_.byte_size());
            }
            else {
                return weight;
            }
        }();
        {
            std::lock_guard lock{mutex_};
            if (!added) {
                if (entry.negative) {
                    --negatives_;
                }
                else {
                    weight_ -= entry.weight;
                }
            }
            if (added) {
                ++entries_;
            }
            bool const reposition = added || (stamp && stamp != entry.stamp) ||
                                    entry.negative != negative;
            if (reposition && !added) {
                unlink(&entry);
            }
            entry.key = &acc->first;
            entry.weight = stored_weight;
            entry.negative = negative;
            if (stamp) {
                entry.stamp = stamp;
            }
            if (negative) {
                entry.stamp = 0;
                ++negatives_;
            }
            else {
                weight_ += stored_weight;
            }
            if (reposition) {
                if (negative) {
                    after(&boundary_, &entry);
                }
                else if (stamp) {
                    after(&head_, &entry);
                }
                else {
                    after(boundary_.prev, &entry);
                }
            }
        }
        acc.release();
        trim();
    }

    void clear()
    {
        map_.clear();
        reset_links();
        weight_ = 0;
        negatives_ = 0;
        entries_ = 0;
    }

    size_t size() const
    {
        return map_.size();
    }

    uint64_t approx_weight() const
    {
        std::lock_guard lock{mutex_};
        return weight_;
    }

    size_t negative_count() const
    {
        std::lock_guard lock{mutex_};
        return negatives_;
    }
};

MONAD_NAMESPACE_END
