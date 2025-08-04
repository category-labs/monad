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
