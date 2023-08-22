#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state/state_changes.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Db
{
    virtual std::optional<Account> read_account(address_t const &) = 0;

    virtual bytes32_t read_storage(
        address_t const &, uint64_t incarnation, bytes32_t const &key) = 0;

    virtual byte_string read_code(bytes32_t const &) = 0;

    virtual void commit(state::StateChanges const &) = 0;

    virtual void
    create_and_prune_block_history(uint64_t block_number) const = 0;
};

MONAD_NAMESPACE_END
