#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/revision.hpp>

#include <utility>

MONAD_EVM_NAMESPACE_BEGIN

enum class Opcode : uint8_t;

template <Revision rev, Opcode op>
struct Trait
{
    static_assert(false, "Trait for opcode unimplemented");
};

MONAD_EVM_NAMESPACE_END
