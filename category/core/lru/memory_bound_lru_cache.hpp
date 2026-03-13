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
#include <memory_resource>
#include <span>

MONAD_NAMESPACE_BEGIN

template <class Key, class KeyHashCompare = tbb::tbb_hash_compare<Key>>
class MemoryBoundLruCache
    : public LruCache<Key, std::pmr::basic_string<uint8_t>, KeyHashCompare>
{
    using Value = std::pmr::basic_string<uint8_t>;
    using Base = LruCache<Key, Value, KeyHashCompare>;

    slab_resource slab_;
    size_t max_bytes_;
    std::atomic<size_t> used_bytes_{0};

public:
    using ConstAccessor = typename Base::ConstAccessor;

    MemoryBoundLruCache(size_t max_bytes, std::span<size_t const> slab_sizes)
        : Base(max_bytes / slab_sizes.front())
        , slab_(slab_sizes)
        , max_bytes_(max_bytes)
    {
        slab_.set_used_bytes(&used_bytes_);
    }

    bool insert(Key const &key, std::span<uint8_t const> data)
    {
        while (used_bytes_.load(std::memory_order_relaxed) >= max_bytes_) {
            if (!Base::evict()) {
                break;
            }
        }
        Value val{data.begin(), data.end(), &slab_};
        return Base::insert(key, std::move(val));
    }

    void clear()
    {
        Base::clear();
        slab_.release();
        used_bytes_.store(0, std::memory_order_relaxed);
    }

    size_t used_bytes() const
    {
        return used_bytes_.load(std::memory_order_relaxed);
    }
};

MONAD_NAMESPACE_END
