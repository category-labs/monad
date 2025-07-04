#pragma once

#include <evmone/baseline.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::evmone
{
    using CodeAnalysis = ::evmone::baseline::CodeAnalysis;

    inline CodeAnalysis analyze(evmc::bytes_view const &code)
    {
        return ::evmone::baseline::analyze(code, false); // TODO eof
    }
}
