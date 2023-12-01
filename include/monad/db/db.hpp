#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>
#include <monad/state2/state_deltas.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Db
{
    virtual std::optional<Account> read_account(Address const &) const = 0;

    virtual bytes32_t
    read_storage(Address const &, bytes32_t const &key) const = 0;

    virtual byte_string read_code(bytes32_t const &) const = 0;

    virtual void commit(StateDeltas const &, Code const &) = 0;

    virtual void
    create_and_prune_block_history(uint64_t block_number) const = 0;
};

MONAD_NAMESPACE_END
