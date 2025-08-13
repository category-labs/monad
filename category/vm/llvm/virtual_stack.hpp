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

        std::tuple<std::int64_t, std::int64_t> deltas(Block const &blk)
        {
            auto [low0, _delta, high0] = blk.stack_deltas();
            auto low = static_cast<std::int64_t>(virt_stack.size()) + low0;
            auto high = static_cast<std::int64_t>(virt_stack.size()) + high0;
            return std::make_tuple(low, high);
        };

        void push(Value *v)
        {
            MONAD_VM_ASSERT(virt_stack.size() < 1024);
            virt_stack.push_back(v);
        };

        Value *pop()
        {
            MONAD_VM_ASSERT(virt_stack.size() > 0);
            auto *v = virt_stack.back();
            virt_stack.pop_back();
            return v;
        };

        void swap(uint8_t i)
        {
            MONAD_VM_ASSERT(i >= 1);
            auto a = virt_stack.size() - 1;
            auto b = a - i;
            std::swap(virt_stack[a], virt_stack[b]);
        };

        void dup(uint8_t i)
        {
            MONAD_VM_ASSERT(i >= 1);
            auto *v = virt_stack[virt_stack.size() - i];
            push(v);
        };

        std::vector<Value *> virt_stack;
    };
}
