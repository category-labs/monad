#pragma once

#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <span>

namespace monad::vm::interpreter
{
    void execute(
        evmc_revision, runtime::Context &, Intercode const &,
        std::uint8_t *stack_ptr);
}
