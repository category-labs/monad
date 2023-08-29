#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/db/db.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

template <class Mutex>
std::optional<Account> &
read_account(address_t const &, StateDeltas &, BlockState<Mutex> &, Db &);

template <class Mutex>
delta_t<bytes32_t> &read_storage(
    address_t const &, uint64_t incarnation, bytes32_t const &location,
    StateDeltas &, BlockState<Mutex> &, Db &);

template <class Mutex>
byte_string& read_code(bytes32_t const &, Code &, BlockState<Mutex> &, Db &);

MONAD_NAMESPACE_END
