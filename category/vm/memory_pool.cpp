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

#include <category/core/runtime/non_temporal_memory.hpp>
#include <category/vm/memory_pool.hpp>

#include <cstdint>
#include <stdatomic.h>

namespace monad::vm
{
    MemoryPool::MemoryPool(std::uint32_t alloc_capacity)
        : empty_head_{.next = &empty_head_}
        , head_{&empty_head_}
        , alloc_capacity_{alloc_capacity}
    {
        MONAD_VM_ASSERT((alloc_capacity & 31) == 0);
    }

    MemoryPool::~MemoryPool()
    {
        Node *n = head_;
        while (n != &empty_head_) {
            auto *const t = n;
            n = n->next;
            std::free(t);
        }
    }

    std::uint8_t *MemoryPool::allocate()
    {
        Node *const prev_head =
            __atomic_exchange_n(&head_, head_->next, __ATOMIC_ACQ_REL);

        if (MONAD_VM_UNLIKELY(prev_head == &empty_head_)) {
            void *const p = std::aligned_alloc(32, alloc_capacity_);
            runtime::non_temporal_bzero(p, alloc_capacity_);
            return reinterpret_cast<std::uint8_t *>(p);
        }

        prev_head->next = nullptr;
        return reinterpret_cast<std::uint8_t *>(prev_head);
    }

    void MemoryPool::deallocate(std::uint8_t *p)
    {
        // This function is based on a cppreference concurrent stack example:
        // https://en.cppreference.com/w/cpp/atomic/atomic/compare_exchange.html

        MONAD_VM_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(p) & 31) == 0);
        static_assert(alignof(Node) <= 32);
        Node *const new_head = reinterpret_cast<Node *>(p);

        new_head->next = __atomic_load_n(&head_, __ATOMIC_RELAXED);
        while (!__atomic_compare_exchange_n(
                    /* ptr: */ &head_,
                    /* expected: */ &new_head->next,
                    /* desired: */ new_head,
                    /* weak: */ true,
                    /* success_memmodel: */ __ATOMIC_RELEASE,
                    /* failure_memmodel: */ __ATOMIC_RELAXED))
        {
            // no-op
        }
    }
}
