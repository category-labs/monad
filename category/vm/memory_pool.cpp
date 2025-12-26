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
#include <category/vm/core/assert.h>
#include <category/vm/memory_pool.hpp>

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <unordered_set>

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

    std::uint8_t *MemoryPool::alloc()
    {
        Node *old_head;
        {
            std::lock_guard const lock{mutex_};
            old_head = head_;
            head_ = old_head->next;
        }

        if (old_head == &empty_head_) {
            void *const p = std::aligned_alloc(32, alloc_capacity_);
            MONAD_VM_ASSERT(p);
            runtime::non_temporal_bzero(p, alloc_capacity_);
            return reinterpret_cast<std::uint8_t *>(p);
        }

        // This clears the memory buffer:
        std::memset(static_cast<void *>(&old_head->next), 0, sizeof(Node *));
        return reinterpret_cast<std::uint8_t *>(old_head);
    }

    void MemoryPool::dealloc(std::uint8_t *p)
    {
        MONAD_VM_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(p) & 31) == 0);
        static_assert(alignof(Node) <= 32);
        Node *const new_head = reinterpret_cast<Node *>(p);
        {
            std::lock_guard const lock{mutex_};
            new_head->next = head_;
            head_ = new_head;
        }
    }

    bool MemoryPool::debug_check_uniqueness_invariant() const
    {
        std::unordered_set<Node *> nodes;
        Node *n = head_;
        while (n != &empty_head_) {
            if (!nodes.insert(n).second) {
                return false;
            }
            n = n->next;
        }
        return true;
    }

    std::size_t MemoryPool::debug_get_cache_size() const
    {
        std::size_t x = 0;
        Node *n = head_;
        while (n != &empty_head_) {
            ++x;
            n = n->next;
        }
        return x;
    }
}
