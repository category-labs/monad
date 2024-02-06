#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/evm/config.hpp>

#include <vector>

MONAD_EVM_NAMESPACE_BEGIN

struct CodeAnalysis
{
    byte_string code;
    std::vector<bool> is_jump_dest;
};

static_assert(sizeof(CodeAnalysis) == 72);
static_assert(alignof(CodeAnalysis) == 8);

CodeAnalysis analyze(byte_string_view const code);

MONAD_EVM_NAMESPACE_END
