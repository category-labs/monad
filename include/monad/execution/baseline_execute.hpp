#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmone/baseline.hpp>

#include <memory>

MONAD_NAMESPACE_BEGIN

evmc::Result baseline_execute(
    evmc_message const &, evmc_revision, evmc::Host *, byte_string_view code,
    std::shared_ptr<evmone::baseline::CodeAnalysis>);

MONAD_NAMESPACE_END
