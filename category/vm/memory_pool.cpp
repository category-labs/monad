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

#include <category/core/assert.h>
#include <category/core/runtime/non_temporal_memory.hpp>
#include <category/vm/memory_pool.hpp>

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <unordered_set>

namespace monad::vm
{
    MemoryPool::MemoryPool(uint32_t const alloc_capacity)
        : empty_head_{.next = &empty_head_}
        , head_{&empty_head_}
        , alloc_capacity_{alloc_capacity}
    {
        MONAD_ASSERT((alloc_capacity & 31) == 0);
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

    uint8_t *MemoryPool::alloc()
    {
        Node *old_head;
        {
            std::lock_guard const lock{mutex_};
            old_head = head_;
            head_ = old_head->next;
        }

        if (old_head == &empty_head_) {
            void *const p = std::aligned_alloc(32, alloc_capacity_);
            MONAD_ASSERT(p);
#if defined(MONAD_ZKVM_ZISK)
            // A freshly allocated buffer already reads as zero on ZisK's
            // prover, so the fill is redundant there.
            //  1. `aligned_alloc` in the guest is `sys_alloc_aligned`, a bump
            //     allocator whose `free` is a no-op (zkvm/core/libc.cpp), so an
            //     address it returns has never been handed out before and
            //     nothing has written to it.
            //  2. ZisK's memory AIR constrains the first access to an address
            //     to read zero when that access is a read:
            //     `addr_changes * (1 - sel) * value[i] === 0` in
            //     state-machines/mem/pil/mem.pil. It is a constraint on the
            //     proof, not a convenience of the emulator, so a prover cannot
            //     answer such a read with anything else.
            //
            // The RECYCLE path below is a different matter and still clears:
            // the buffer it returns has been written, and what makes it zero
            // again is `Memory::clear` on release plus the one pointer word
            // `dealloc` dirtied.
            (void)0;
#else
            runtime::non_temporal_bzero(p, alloc_capacity_);
#endif
            return reinterpret_cast<uint8_t *>(p);
        }

        // This clears the memory buffer:
        std::memset(static_cast<void *>(&old_head->next), 0, sizeof(Node *));
        return reinterpret_cast<uint8_t *>(old_head);
    }

    void MemoryPool::dealloc(uint8_t *const p)
    {
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(p) & 31) == 0);
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

    size_t MemoryPool::debug_get_cache_size() const
    {
        size_t x = 0;
        Node *n = head_;
        while (n != &empty_head_) {
            ++x;
            n = n->next;
        }
        return x;
    }
}
