#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/vm/vm.hpp>

#include <cstdint>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Db
{
    virtual std::optional<Account> read_account(Address const &) = 0;

    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) = 0;

    virtual vm::SharedIntercode read_code(bytes32_t const &) = 0;

    virtual BlockHeader read_eth_header() = 0;
    virtual bytes32_t state_root() = 0;
    virtual bytes32_t receipts_root() = 0;
    virtual bytes32_t transactions_root() = 0;
    virtual std::optional<bytes32_t> withdrawals_root() = 0;

    virtual void set_block_and_round(
        uint64_t block_number,
        std::optional<uint64_t> round_number = std::nullopt) = 0;
    virtual void finalize(uint64_t block_number, uint64_t round_number) = 0;
    virtual void update_verified_block(uint64_t block_number) = 0;
    virtual void
    update_voted_metadata(uint64_t block_number, uint64_t round) = 0;
    virtual void
    update_proposed_metadata(uint64_t block_number, uint64_t round) = 0;

    virtual void commit(
        StateDeltas const &, Code const &, MonadConsensusBlockHeader const &,
        std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt) = 0;

    virtual void commit(
        std::unique_ptr<StateDeltas> state_deltas, Code const &code,
        MonadConsensusBlockHeader const &consensus_header,
        std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &transactions = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals = {})
    {
        commit(
            *state_deltas,
            code,
            consensus_header,
            receipts,
            call_frames,
            senders,
            transactions,
            ommers,
            withdrawals);
    }

    virtual std::string print_stats()
    {
        return {};
    }
};

MONAD_NAMESPACE_END
