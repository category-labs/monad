#pragma once

#include <monad/evm/config.hpp>

#include <utility>

MONAD_EVM_NAMESPACE_BEGIN

enum class Opcode : uint8_t;

template <Opcode op>
struct Trait
{
    static_assert(false, "Trait for opcode unimplemented");
};

MONAD_EVM_NAMESPACE_END
