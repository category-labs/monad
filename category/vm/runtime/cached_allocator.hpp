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

#include <category/vm/core/assert.h>
#include <category/vm/runtime/uint256.hpp>

#include <cstdlib>
#include <functional>
#include <memory>
#include <vector>

namespace monad::vm::runtime
{
    struct CachedAllocatorElement
    {
        CachedAllocatorElement *next;
        size_t idx;
    };

    class CachedAllocatorList
    {
        CachedAllocatorElement *elements;

    public:
        CachedAllocatorList()
            : elements{nullptr}
        {
        }

        [[gnu::always_inline]]
        bool empty()
        {
            return elements == nullptr;
        }

        [[gnu::always_inline]]
        size_t size()
        {
            return empty() ? 0 : elements->idx;
        }

        void push(CachedAllocatorElement *e)
        {
            e->next = elements;
            e->idx = size() + 1;
            elements = e;
        }

        CachedAllocatorElement *pop()
        {
            MONAD_VM_DEBUG_ASSERT(!empty());
            auto *ptr = elements;
            elements = ptr->next;
            return ptr;
        }

        ~CachedAllocatorList()
        {
            auto *e = elements;
            while (e) {
                auto *next = e->next;
                std::free(e);
                e = next;
            }
        }
    };

    template <typename T>
    concept CachedAllocable = requires {
        typename T::base_type;
        { T::size } -> std::same_as<size_t const &>;
        { T::alignment } -> std::same_as<size_t const &>;
        { T::cache_list } -> std::same_as<CachedAllocatorList &>;
    };

    template <CachedAllocable T>
    class CachedAllocator
    {
    public:
        static constexpr size_t alloc_size =
            sizeof(typename T::base_type) * T::size;
        static constexpr size_t DEFAULT_MAX_CACHE_BYTE_SIZE = 256 * alloc_size;

        static_assert(alloc_size % T::alignment == 0);
        static_assert(sizeof(CachedAllocatorElement) <= alloc_size);

        /// Create an allocator which will allow up to
        /// `max_cache_byte_size_per_thread` number of bytes being
        /// consumed by each (thread local) cache.
        constexpr explicit CachedAllocator(
            size_t max_cache_byte_size_per_thread = DEFAULT_MAX_CACHE_BYTE_SIZE)
        {
            max_slots_in_cache = max_cache_byte_size_per_thread / alloc_size;
        };

        uint8_t *aligned_alloc_cached() const
        {
            if (T::cache_list.empty()) {
                return reinterpret_cast<uint8_t *>(
                    std::aligned_alloc(T::alignment, alloc_size));
            }
            else {
                return reinterpret_cast<uint8_t *>(T::cache_list.pop());
            }
        }

        /// Free memory allocated with `aligned_alloc_cached`.
        void free_cached(uint8_t *ptr) const
        {
            if (T::cache_list.size() >= max_slots_in_cache) {
                std::free(ptr);
            }
            else {
                T::cache_list.push(
                    reinterpret_cast<CachedAllocatorElement *>(ptr));
            }
        };

        std::unique_ptr<uint8_t, std::function<void(uint8_t *)>>
        allocate() const
        {
            return {aligned_alloc_cached(), [*this](uint8_t *ptr) {
                        free_cached(ptr);
                    }};
        }

    private:
        /// Upper bound on the number of elements in each cache.
        size_t max_slots_in_cache;
    };
}
