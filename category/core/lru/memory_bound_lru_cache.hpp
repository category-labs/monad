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

#include <category/core/lru/lru_cache.hpp>
#include <category/core/mem/slab_resource.hpp>

#include <atomic>
#include <cstddef>
#include <memory>
#include <memory_resource>
#include <span>

MONAD_NAMESPACE_BEGIN

template <class Key, class KeyHashCompare = tbb::tbb_hash_compare<Key>>
class MemoryBoundLruCache
{
    using Value = std::pmr::basic_string<uint8_t>;
    using Lru = LruCache<Key, Value, KeyHashCompare>;

public:
    struct TierConfig
    {
        size_t slab_size;
        size_t max_bytes;
    };

    using ConstAccessor = typename Lru::ConstAccessor;

private:
    struct Tier
    {
        size_t slab_size;
        std::unique_ptr<Lru> lru;

        Tier(size_t slab_sz, size_t max_entries)
            : slab_size(slab_sz)
            , lru(std::make_unique<Lru>(max_entries))
        {
        }
    };

    slab_resource slab_;
    size_t max_bytes_;
    std::vector<Tier> tiers_;

public:
    MemoryBoundLruCache(std::span<TierConfig const> configs)
        : max_bytes_(0)
    {
        tiers_.reserve(configs.size());
        for (auto const &cfg : configs) {
            max_bytes_ += cfg.max_bytes;
            tiers_.emplace_back(cfg.slab_size, cfg.max_bytes / cfg.slab_size);
        }
    }

    bool find(ConstAccessor &acc, Key const &key)
    {
        for (auto &tier : tiers_) {
            if (tier.lru->find(acc, key)) {
                return true;
            }
        }
        return false;
    }

    bool insert(Key const &key, std::span<uint8_t const> data)
    {
        size_t const idx = tier_index(data.size());
        auto &tier = tiers_[idx];

        while (slab_.used_bytes() >= max_bytes_) {
            if (!evict_from(idx)) {
                break;
            }
        }

        Value val{data.begin(), data.end(), &slab_};
        return tier.lru->insert_construct(key, std::move(val));
    }

    void clear()
    {
        for (auto &tier : tiers_) {
            tier.lru->clear();
        }
        slab_.release();
    }

    size_t used_bytes() const
    {
        return slab_.used_bytes();
    }

    std::string print_stats()
    {
        std::string s;
        for (auto &tier : tiers_) {
            if (!s.empty()) {
                s += '/';
            }
            s += tier.lru->print_stats();
        }
        return s;
    }

private:
    size_t tier_index(size_t bytes) const
    {
        for (size_t i = 0; i < tiers_.size(); ++i) {
            if (bytes <= tiers_[i].slab_size) {
                return i;
            }
        }
        return tiers_.size() - 1;
    }

    bool evict_from(size_t start)
    {
        for (size_t i = 0; i < tiers_.size(); ++i) {
            size_t const idx = (start + i) % tiers_.size();
            if (tiers_[idx].lru->evict()) {
                return true;
            }
        }
        return false;
    }
};

MONAD_NAMESPACE_END
