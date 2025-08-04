#pragma once

#include <category/vm/evmone/code_analysis.hpp>

#include <evmc/evmc.hpp>

namespace monad::vm::evmone
{
    evmc::Result baseline_execute(
        evmc_message const &msg, evmc_revision const rev,
        evmc::Host *const host, CodeAnalysis const &code_analysis);
}
