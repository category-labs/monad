#pragma once

#include <monad/config.hpp>

#include <evmone/baseline.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using CodeAnalysis = ::evmone::baseline::CodeAnalysis;

inline CodeAnalysis analyze(byte_string_view const &code)
{
    return evmone::baseline::analyze(code, false); // TODO eof
}

MONAD_NAMESPACE_END
