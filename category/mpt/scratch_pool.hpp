// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/core/thread_local.h>
#include <category/mpt/config.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdlib>
#include <new>

MONAD_MPT_NAMESPACE_BEGIN

// Per-thread free lists for the short-lived scratch objects of an upsert
// (tnodes and child arrays), bucketed by size. A block is cached by the thread
// that frees it, which need not be the thread that allocated it.
class ScratchPool
{
public:
    static constexpr size_t granule = 64;
    // Larger blocks bypass the cache.
    static constexpr size_t max_cached_block = 2048;
    static constexpr size_t max_cached_bytes = 4 * 1024 * 1024;
    // ASAN builds send every block to malloc, so that use-after-free and
    // overflow into the size-class slack are still reported.
#ifdef MONAD_HAVE_ASAN
    static constexpr bool caching = false;
#else
    static constexpr bool caching = true;
#endif

    ScratchPool() = default;
    ScratchPool(ScratchPool const &) = delete;
    ScratchPool &operator=(ScratchPool const &) = delete;

    ~ScratchPool()
    {
        for (FreeBlock *&head : free_) {
            while (head != nullptr) {
                FreeBlock *const next = head->next;
                std::free(head);
                head = next;
            }
        }
    }

    [[nodiscard]] void *allocate(size_t const bytes)
    {
        if (!caching || bytes > max_cached_block) {
            return checked_malloc(bytes);
        }
        size_t const cls = size_class(bytes);
        FreeBlock *const block = free_[cls];
        if (block == nullptr) {
            return checked_malloc(class_bytes(cls));
        }
        free_[cls] = block->next;
        cached_bytes_ -= class_bytes(cls);
        return block;
    }

    void deallocate(void *const p, size_t const bytes) noexcept
    {
        size_t const cls = size_class(bytes);
        if (!caching || bytes > max_cached_block ||
            cached_bytes_ + class_bytes(cls) > max_cached_bytes) {
            std::free(p);
            return;
        }
        free_[cls] = ::new (p) FreeBlock{free_[cls]};
        cached_bytes_ += class_bytes(cls);
    }

    size_t cached_bytes() const noexcept
    {
        return cached_bytes_;
    }

    static ScratchPool &local() noexcept
    {
        static MONAD_THREAD_LOCAL ScratchPool pool;
        return pool;
    }

private:
    struct FreeBlock
    {
        FreeBlock *next;
    };

    static constexpr size_t num_classes = max_cached_block / granule;

    std::array<FreeBlock *, num_classes> free_{};
    size_t cached_bytes_{0};

    static constexpr size_t size_class(size_t const bytes) noexcept
    {
        return bytes == 0 ? 0 : (bytes - 1) / granule;
    }

    static constexpr size_t class_bytes(size_t const cls) noexcept
    {
        return (cls + 1) * granule;
    }

    static void *checked_malloc(size_t const bytes)
    {
        void *const p = std::malloc(std::max(bytes, size_t{1}));
        MONAD_ASSERT(p != nullptr);
        return p;
    }
};

template <class T>
struct ScratchAllocator
{
    using value_type = T;

    constexpr ScratchAllocator() noexcept = default;

    template <class U>
    // NOLINTNEXTLINE(google-explicit-constructor)
    constexpr ScratchAllocator(ScratchAllocator<U> const &) noexcept
    {
    }

    [[nodiscard]] T *allocate(size_t const n)
    {
        static_assert(alignof(T) <= alignof(std::max_align_t));
        return static_cast<T *>(ScratchPool::local().allocate(n * sizeof(T)));
    }

    void deallocate(T *const p, size_t const n) noexcept
    {
        ScratchPool::local().deallocate(p, n * sizeof(T));
    }

    template <class U>
    constexpr bool operator==(ScratchAllocator<U> const &) const noexcept
    {
        return true;
    }
};

MONAD_MPT_NAMESPACE_END
