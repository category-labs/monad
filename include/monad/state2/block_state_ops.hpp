#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Account> &
read_account(address_t const &, StateDeltas &, BlockState &);

Delta<bytes32_t> &read_storage(
    address_t const &, uint64_t incarnation, bytes32_t const &location,
    StateDeltas &, BlockState &);

byte_string &read_code(bytes32_t const &, Code &, BlockState &);

MONAD_NAMESPACE_END
