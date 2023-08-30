#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

template <class Mutex>
std::optional<Account> &
read_account(address_t const &, State &, BlockState<Mutex> &, Db &);

template <class Mutex>
delta_t<bytes32_t> &read_storage(
    address_t const &, uint64_t incarnation, bytes32_t const &location, State &,
    BlockState<Mutex> &, Db &);

MONAD_NAMESPACE_END
