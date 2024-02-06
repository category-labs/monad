#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/memory.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// 9.4.1
struct MachineState
{
    uint64_t gas_left; // g
    size_t pc; // pc
    Memory memory; // m
    uint256_t stack[1024]; // s
};

static_assert(sizeof(MachineState) == 32816);
static_assert(alignof(MachineState) == 8);

MONAD_EVM_NAMESPACE_END
