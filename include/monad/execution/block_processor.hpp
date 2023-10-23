#pragma once

#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

#include <monad/logging/formatter.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <boost/fiber/all.hpp>
#include <quill/Quill.h>

#include <chrono>
#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

struct AllTxnBlockProcessor
{
    template <class TMutex, class TTraits, class TxnProcData>
    [[nodiscard]] std::vector<Receipt>
    execute(Block &b, Db &db, BlockHashBuffer const &block_hash_buffer)
    {
        auto const start_time = std::chrono::steady_clock::now();
        LOG_INFO(
            "Start executing Block {}, with {} transactions",
            b.header.number,
            b.transactions.size());
        LOG_DEBUG("BlockHeader Fields: {}", b.header);

        BlockState<TMutex> block_state{};

        // Apply DAO hack reversal
        TTraits::transfer_balance_dao(block_state, db, b.header.number);

        std::vector<Receipt> r{};
        r.reserve(b.transactions.size());

        for (unsigned i = 0; i < b.transactions.size(); ++i) {
            b.transactions[i].from = recover_sender(b.transactions[i]);
            TxnProcData txn_executor{
                db,
                block_state,
                b.transactions[i],
                b.header,
                block_hash_buffer,
                i};
            txn_executor.validate_and_execute();
            auto &[receipt, state] = txn_executor.result_;

            LOG_DEBUG("State Deltas: {}", state.state_);
            LOG_DEBUG("Code Deltas: {}", state.code_);

            auto const reward = TTraits::calculate_txn_award(
                b.transactions[i],
                b.header.base_fee_per_gas.value_or(0),
                receipt.gas_used);
            state.add_to_balance(b.header.beneficiary, reward);
            TTraits::destruct_touched_dead(state);

            MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
            merge(block_state.state, state.state_);
            merge(block_state.code, state.code_);

            r.push_back(receipt);
        }

        // Process withdrawls
        state::State state{block_state, db};
        TTraits::process_withdrawal(state, b.withdrawals);

        // Apply block reward to beneficiary
        TTraits::apply_block_award(block_state, db, b);

        TTraits::destruct_touched_dead(state);
        MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
        merge(block_state.state, state.state_);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        LOG_INFO(
            "Finish executing Block {}, time elapsed = {}",
            b.header.number,
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
