#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

evmc::Result baseline_execute(
    evmc_message const &, evmc_revision, evmc::Host *, byte_string_view code);

MONAD_NAMESPACE_END
