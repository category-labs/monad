#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/config.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/state2/state_deltas.hpp>

#include <cstdint>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Db
{
    virtual std::optional<Account> read_account(Address const &) = 0;

    virtual bytes32_t read_storage(Address const &, bytes32_t const &key) = 0;

    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) = 0;

    virtual void increment_block_number() = 0;

    virtual void commit(
        StateDeltas const &, Code const &,
        std::vector<Receipt> const & = {}) = 0;

    virtual bytes32_t state_root() = 0;
    virtual bytes32_t receipts_root() = 0;

    virtual void
    create_and_prune_block_history(uint64_t block_number) const = 0;
};

MONAD_NAMESPACE_END
