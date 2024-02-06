#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/evm/revision.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

class State;

evmc::Result baseline_execute(
    evmc_message const &, evmc_revision, evmc::Host *, CodeAnalysis const &);

// TODO: get rid of the evmc type
template <evm::Revision rev>
evmc::Result monad_execute(
    State &, BlockHeader const &, byte_string_view code, Address const &sender,
    Address const &origin, Address const &recipient, uint64_t gas,
    uint256_t const &value, uint256_t const &gas_price,
    byte_string_view input_data, size_t depth, bool can_modify_state);

MONAD_NAMESPACE_END
