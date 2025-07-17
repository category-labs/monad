#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
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

    // empty block_id represents the finalized block
    virtual void set_block_and_prefix(
        uint64_t block_number, bytes32_t const &block_id = bytes32_t{}) = 0;
    virtual void finalize(uint64_t block_number, bytes32_t const &block_id) = 0;
    virtual void update_verified_block(uint64_t block_number) = 0;
    virtual void
    update_voted_metadata(uint64_t block_number, bytes32_t const &block_id) = 0;

    virtual void commit(
        StateDeltas const &, Code const &, bytes32_t const &block_id,
        BlockHeader const &, std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt) = 0;

    virtual void commit(
        std::unique_ptr<StateDeltas> state_deltas, Code const &code,
        bytes32_t const &block_id, BlockHeader const &header,
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
            block_id,
            header,
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
