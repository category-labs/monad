#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/state2/state_deltas.hpp>

#include <cstdint>
#include <memory>
#include <optional>

#define MMM_DIFF 1

MONAD_NAMESPACE_BEGIN

struct Db
{
    virtual std::optional<Account> read_account(Address const &) = 0;

    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) = 0;

    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) = 0;

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

    virtual void commit(
        StateDeltas const &, Code const &, BlockHeader const &,
        std::vector<Receipt> const & = {}, bytes32_t const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt,
        std::optional<uint64_t> round_number = std::nullopt) = 0;

    virtual void commit(
        std::unique_ptr<StateDeltas> &state_deltas, std::unique_ptr<Code> &code,
        BlockHeader const &header, std::vector<Receipt> const &receipts,
        bytes32_t const &bft_block_id,
        std::vector<std::vector<CallFrame>> const &call_frames,
        std::vector<Transaction> const &transactions,
        std::vector<BlockHeader> const &ommers,
        std::optional<std::vector<Withdrawal>> const &withdrawals,
        std::optional<uint64_t> const round_number)
    {
        commit(
            *state_deltas,
            *code,
            header,
            receipts,
            bft_block_id,
            call_frames,
            transactions,
            ommers,
            withdrawals,
            round_number);
    }

    virtual std::string print_stats()
    {
        return {};
    }
};

MONAD_NAMESPACE_END
