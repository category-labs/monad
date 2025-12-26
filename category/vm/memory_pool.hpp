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
        class Ref
        {
            MemoryPool &pool_;
            std::uint8_t *memory_;

        public:
            Ref(MemoryPool &pool)
                : pool_{pool}
                , memory_{pool.allocate()}
            {
            }
            
            ~Ref()
            {
                pool_.deallocate(memory_);
            }

            std::uint8_t *get()
            {
                return memory_;
            }
        };

        MemoryPool(std::uint32_t alloc_capacity);

        MemoryPool(MemoryPool const&) = delete;
        MemoryPool &operator=(MemoryPool const&) = delete;

        ~MemoryPool();

        std::uint8_t *allocate();

        void deallocate(std::uint8_t *);

        Ref alloca()
        {
            return Ref{*this};
        }

        std::uint32_t alloc_capacity() const
        {
            return alloc_capacity_;
        }

    private:
        Node empty_head_;
        Node *head_;
        std::uint32_t alloc_capacity_;
    };
}
