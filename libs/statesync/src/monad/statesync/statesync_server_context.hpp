#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/db/db.hpp>
#include <monad/mpt/db.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <oneapi/tbb/concurrent_hash_map.h>
#pragma GCC diagnostic pop

#include <vector>

MONAD_NAMESPACE_BEGIN

using Deleted = oneapi::tbb::concurrent_hash_map<
    uint64_t, std::vector<std::pair<Address, std::vector<bytes32_t>>>>;

struct CallFrame;
class TrieDb;

MONAD_NAMESPACE_END

struct monad_statesync_server_context final : public monad::Db
{
    monad::TrieDb &rw;
    monad::mpt::Db *ro;
    monad::Deleted deleted;

    explicit monad_statesync_server_context(monad::TrieDb &rw);

    virtual std::optional<monad::Account>
    read_account(monad::Address const &addr) override;

    virtual monad::bytes32_t read_storage(
        monad::Address const &addr, monad::Incarnation,
        monad::bytes32_t const &key) override;

    virtual std::shared_ptr<monad::CodeAnalysis>
    read_code(monad::bytes32_t const &hash) override;

    virtual monad::BlockHeader read_eth_header() override;

    virtual monad::bytes32_t state_root() override;

    virtual monad::bytes32_t receipts_root() override;

    virtual monad::bytes32_t transactions_root() override;

    virtual std::optional<monad::bytes32_t> withdrawals_root() override;

    virtual void set_block_and_round(
        uint64_t block_number,
        std::optional<uint64_t> round_number = std::nullopt) override;
    virtual void
    finalize(uint64_t block_number, uint64_t round_number) override;
    virtual void update_verified_block(uint64_t) override;

    virtual void commit(
        monad::StateDeltas const &state_deltas, monad::Code const &code,
        monad::BlockHeader const &,
        std::vector<monad::Receipt> const &receipts = {},
        std::vector<std::vector<monad::CallFrame>> const & = {},
        std::vector<monad::Transaction> const &transactions = {},
        std::vector<monad::BlockHeader> const &ommers = {},
        std::optional<std::vector<monad::Withdrawal>> const & = std::nullopt,
        std::optional<uint64_t> round_number = std::nullopt) override;
};
