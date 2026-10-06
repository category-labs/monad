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

#include <category/core/asan.h>
#include <category/core/assert.h>

#include <concepts>
#include <cstddef>
#include <cstdlib>
#include <memory>
#include <new>
#include <type_traits>

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
            if (empty()) {
                return 0;
            }
            MONAD_ASAN_UNPOISON(elements, sizeof(CachedAllocatorElement));
            size_t const n = elements->idx;
            MONAD_ASAN_POISON(elements, sizeof(CachedAllocatorElement));
            return n;
        }

        void push(void *const storage)
        {
            auto const new_size = size() + 1;
            elements = ::new (storage)
                CachedAllocatorElement{.next = elements, .idx = new_size};
            MONAD_ASAN_POISON(storage, sizeof(CachedAllocatorElement));
        }

        CachedAllocatorElement *pop()
        {
            MONAD_DEBUG_ASSERT(!empty());
            auto *ptr = elements;
            MONAD_ASAN_UNPOISON(ptr, sizeof(CachedAllocatorElement));
            elements = ptr->next;
            return ptr;
        }

        ~CachedAllocatorList()
        {
            auto *e = elements;
            while (e) {
                MONAD_ASAN_UNPOISON(e, sizeof(CachedAllocatorElement));
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
        using base_type = typename T::base_type;

        static constexpr size_t alloc_size = sizeof(base_type) * T::size;
        static constexpr size_t DEFAULT_MAX_CACHE_BYTE_SIZE = 4096 * alloc_size;

        struct Deleter
        {
            size_t const max_slots_in_cache;

            void operator()(void *const storage) const
            {
                if (T::cache_list.size() >= max_slots_in_cache) {
                    std::free(storage);
                }
                else {
                    T::cache_list.push(storage);
                    MONAD_ASAN_POISON(storage, alloc_size);
                }
            }
        };

#if defined(__cpp_lib_is_implicit_lifetime) &&                                 \
    __cpp_lib_is_implicit_lifetime >= 202302L
        static_assert(std::is_implicit_lifetime_v<base_type>);
#else
        static_assert(std::is_trivially_copy_constructible_v<base_type>);
#endif
        // Cached storage is reused without calling payload destructors.
        static_assert(std::is_trivially_destructible_v<base_type>);

        static_assert(T::alignment >= 32);
        static_assert(alignof(base_type) <= T::alignment);
        static_assert(alignof(CachedAllocatorElement) <= T::alignment);
        static_assert(alloc_size % T::alignment == 0);
        static_assert(sizeof(CachedAllocatorElement) <= alloc_size);

        /// Create an allocator which will allow up to
        /// `max_cache_byte_size_per_thread` number of bytes being
        /// consumed by each (thread local) cache.
        constexpr explicit CachedAllocator(
            size_t const max_cache_byte_size_per_thread =
                DEFAULT_MAX_CACHE_BYTE_SIZE)
        {
            max_slots_in_cache = max_cache_byte_size_per_thread / alloc_size;
        };

        std::byte *aligned_alloc_cached() const
        {
            void *storage;
            if (T::cache_list.empty()) {
                storage = std::aligned_alloc(T::alignment, alloc_size);
            }
            else {
                storage = T::cache_list.pop();
                MONAD_ASAN_UNPOISON(storage, alloc_size);
            }

            MONAD_ASSERT(storage != nullptr);

            // Start byte storage and implicitly create payload objects without
            // initializing their values.
            return ::new (storage) std::byte[alloc_size];
        }

        /// Clear cache for testing/debugging purposes
        void debug_clear_cache() const
        {
            while (!T::cache_list.empty()) {
                std::free(T::cache_list.pop());
            }
        }

        /// Free memory allocated with `aligned_alloc_cached`.
        void free_cached(void *const storage) const
        {
            Deleter{max_slots_in_cache}(storage);
        };

        /// Return live base_type objects whose values are uninitialized.
        std::unique_ptr<base_type, Deleter> allocate() const
        {
            // aligned_alloc_cached's placement new of a std::byte array
            // implicitly creates the base_type objects. reinterpret_cast alone
            // does not retarget the byte pointer to those objects; launder
            // obtains a pointer to the first live base_type. Its lifetime has
            // already started before the call to launder.
            auto *const ptr = std::launder(
                reinterpret_cast<base_type *>(aligned_alloc_cached()));
            return {ptr, Deleter{max_slots_in_cache}};
        }

    private:
        /// Upper bound on the number of elements in each cache.
        size_t max_slots_in_cache;
    };
}
