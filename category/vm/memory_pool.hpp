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

#include <category/core/synchronization/spin_lock.hpp>

#include <cstdint>

namespace monad::vm
{
    class MemoryPool
    {
        struct Node
        {
            Node *next;
        };

    public:
        // A memory buffer "unique pointer":
        class Ref
        {
            MemoryPool &pool_;
            std::uint8_t *memory_;

        public:
            explicit Ref(MemoryPool &pool)
                : pool_{pool}
                , memory_{pool.alloc()}
            {
            }

            Ref(Ref const &) = delete;
            Ref(Ref &&) = delete;
            Ref &operator=(Ref const &) = delete;
            Ref &operator=(Ref &&) = delete;

            ~Ref()
            {
                pool_.dealloc(memory_);
            }

            std::uint8_t *get()
            {
                return memory_;
            }
        };

        // Construct a memory pool with the given `alloc_capacity()`.
        explicit MemoryPool(std::uint32_t alloc_capacity);

        MemoryPool(MemoryPool const &) = delete;
        MemoryPool &operator=(MemoryPool const &) = delete;

        ~MemoryPool();

        // Capacity of memory buffer returned by `alloc()` and `alloc_ref()`.
        std::uint32_t alloc_capacity() const
        {
            return alloc_capacity_;
        }

        // Allocate zero initialized memory buffer of `alloc_capacity()` size.
        std::uint8_t *alloc();

        // Deallocate memory previous allocated with `alloc()`. Make sure
        // the entire memory buffer is zeroed before calling `dealloc()`.
        void dealloc(std::uint8_t *);

        // Allocate zero initialized memory buffer of `alloc_capacity()` size.
        // The entire memory buffer must be zeroed before the `Ref` object is
        // destroyed.
        Ref alloc_ref()
        {
            return Ref{*this};
        }

        // Debugging/testing:
        bool debug_check_uniqueness_invariant() const;
        std::size_t debug_get_cache_size() const;

    private:
        Node empty_head_;
        Node *head_;
        std::uint32_t alloc_capacity_;
        SpinLock mutex_;
    };
}
