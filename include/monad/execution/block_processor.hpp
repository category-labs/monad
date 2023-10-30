#pragma once

#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/validation_status.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <boost/fiber/all.hpp>
#include <quill/Quill.h>
#include <tl/expected.hpp>

#include <chrono>
#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

struct AllTxnBlockProcessor
{
    // EIP-4895
    template <class TState>
    static void process_withdrawal(
        TState &state,
        std::optional<std::vector<Withdrawal>> const &withdrawals)
    {
        if (withdrawals.has_value()) {
            for (auto const &withdrawal : withdrawals.value()) {
                state.add_to_balance(
                    withdrawal.recipient,
                    uint256_t{withdrawal.amount} * uint256_t{1'000'000'000u});
            }
        }
    }
    template <class TMutex, class TTraits, class TxnProcData>
    [[nodiscard]] tl::expected<std::vector<Receipt>, ValidationStatus>
    execute(Block &block, Db &db, BlockHashBuffer const &block_hash_buffer)
    {
        auto const start_time = std::chrono::steady_clock::now();
        LOG_INFO(
            "Start executing Block {}, with {} transactions",
            block.header.number,
            block.transactions.size());
        LOG_DEBUG("BlockHeader Fields: {}", block.header);

        BlockState<TMutex> block_state{};

        // Apply DAO hack reversal
        TTraits::transfer_balance_dao(block_state, db, block.header.number);

        std::vector<Receipt> r{};
        r.reserve(block.transactions.size());

        for (unsigned i = 0; i < block.transactions.size(); ++i) {
            block.transactions[i].from = recover_sender(block.transactions[i]);
            TxnProcData txn_executor{
                db,
                block_state,
                block.transactions[i],
                block.header,
                block_hash_buffer,
                i};

            if (auto const txn_status =
                    txn_executor.template validate_and_execute<TTraits>();
                txn_status != ValidationStatus::SUCCESS) {
                return tl::unexpected(txn_status);
            }
            auto &[receipt, state] = txn_executor.result_;

            LOG_DEBUG("State Deltas: {}", state.state_);
            LOG_DEBUG("Code Deltas: {}", state.code_);

            MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
            merge(block_state.state, state.state_);
            merge(block_state.code, state.code_);

            r.push_back(receipt);
        }

        State state{block_state, db};
        if constexpr (TTraits::rev >= EVMC_SHANGHAI) {
            process_withdrawal(state, block.withdrawals);
        }

        TTraits::apply_block_award(block_state, db, block);

        if constexpr (TTraits::rev >= EVMC_SPURIOUS_DRAGON) {
            state.destruct_touched_dead();
        }
        MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
        merge(block_state.state, state.state_);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        LOG_INFO(
            "Finish executing Block {}, time elapsed = {}",
            block.header.number,
            elapsed_ms);
        LOG_DEBUG("Receipts: {}", r);

        commit(block_state, db);

        return r;
    }

    template <class TMutex>
    void commit(BlockState<TMutex> &block_state, Db &db)
    {
        auto const start_time = std::chrono::steady_clock::now();
        LOG_INFO("{}", "Committing to DB...");

        db.commit(block_state.state, block_state.code);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        LOG_INFO("Finished committing, time elapsed = {}", elapsed_ms);
    }
};

MONAD_EXECUTION_NAMESPACE_END
