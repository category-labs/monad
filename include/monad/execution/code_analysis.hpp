#pragma once

#include <monad/config.hpp>

#include <evmone/baseline.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using CodeAnalysis = ::evmone::baseline::CodeAnalysis;

inline CodeAnalysis analyze(byte_string_view const &code)
{
    return evmone::baseline::analyze(EVMC_FRONTIER, code); // TODO rev
}

MONAD_NAMESPACE_END
