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

#include <category/vm/compiler/ir/basic_blocks.hpp>

namespace monad::vm::llvm
{
    using namespace monad::vm::compiler::basic_blocks;

    struct VirtualStack
    {
    public:
        void clear()
        {
            virt_stack.clear();
        };

        void push(Value *v)
        {
            MONAD_VM_ASSERT(size() < 1024);
            virt_stack.push_back(v);
        };

        void push_front(Value *v)
        {
            MONAD_VM_ASSERT(size() < 1024);
            virt_stack.insert(virt_stack.begin(), v);
        };

        int64_t size() const
        {
            return static_cast<int64_t>(virt_stack.size());
        };

        Value *peek(int64_t i) const
        {
            int64_t const sz = size();
            int64_t const ix = sz + i;
            MONAD_VM_ASSERT(ix >= 0);
            MONAD_VM_ASSERT(ix < sz);
            return virt_stack[static_cast<size_t>(ix)];
        };

        Value *pop()
        {
            MONAD_VM_ASSERT(size() > 0);
            auto *v = virt_stack.back();
            virt_stack.pop_back();
            return v;
        };

        void swap(uint8_t i)
        {
            MONAD_VM_ASSERT(i >= 1);
            int64_t const a = size() - 1;
            int64_t const b = a - i;
            std::swap(
                virt_stack[static_cast<size_t>(a)],
                virt_stack[static_cast<size_t>(b)]);
        };

        void dup(uint8_t i)
        {
            MONAD_VM_ASSERT(i >= 1);
            auto *v = virt_stack[static_cast<size_t>(size() - i)];
            push(v);
        };

        std::vector<Value *> virt_stack;
    };
}
