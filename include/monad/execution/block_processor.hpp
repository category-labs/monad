#pragma once

#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

#include <monad/logging/monad_log.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <chrono>
#include <vector>

#include <boost/fiber/all.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TResult, class TFnObject>
struct PromiseReturningInvocable
{
    boost::fibers::promise<TResult> p_;
    TFnObject obj_;

    PromiseReturningInvocable(
        boost::fibers::promise<TResult> &&p, TFnObject &&obj)
        : p_{std::move(p)}
        , obj_{std::move(obj)}
    {
    }

    void operator()()
    {
        obj_();
        p_.set_value(std::move(obj_.get_result()));
    }
};

struct AllTxnBlockProcessor
{
    template <class TMutex, class TTraits, class TxnProcData, class TBlockCache>
    [[nodiscard]] std::vector<Receipt>
    execute(Block &b, Db &db, TBlockCache &block_cache)
    {
        using result_t = typename TxnProcData::result_t;
        using obj_task_t = PromiseReturningInvocable<result_t, TxnProcData>;

        auto *block_logger = log::logger_t::get_logger("block_logger");
        auto const start_time = std::chrono::steady_clock::now();
        MONAD_LOG_INFO(
            block_logger,
            "Start executing Block {}, with {} transactions",
            b.header.number,
            b.transactions.size());
        MONAD_LOG_DEBUG(block_logger, "BlockHeader Fields: {}", b.header);

        BlockState<TMutex> block_state{};
        uint256_t all_txn_gas_reward = 0;

        // Apply DAO hack reversal
        TTraits::transfer_balance_dao(
            block_state, db, block_cache, b.header.number);

        std::vector<boost::fibers::future<result_t>> futures{};
        std::vector<boost::fibers::fiber> fibers{};
        std::vector<Receipt> r{};

        futures.reserve(b.transactions.size());
        fibers.reserve(b.transactions.size());
        r.reserve(b.transactions.size());

        // Construct fibers from all transactions
        for (unsigned index = 0u; auto &txn : b.transactions) {
            txn.from = recover_sender(txn);
            boost::fibers::promise<result_t> p{};
            futures.push_back(p.get_future());
            TxnProcData data{
                db, block_state, txn, b.header, block_cache, index};
            obj_task_t t{std::move(p), std::move(data)};
            fibers.emplace_back(std::move(t));
            ++index;
        }

        // Merge in order, or re-run if necessary
        for (unsigned index = 0u; auto &future : futures) {
            auto txn_result = future.get();
            auto &result = txn_result.first;
            auto &state = txn_result.second;

            if (std::shared_lock<TMutex> const lock{block_state.mutex};
                can_merge(block_state.state, state.state_)) {
                merge(block_state.state, state.state_);
                merge(block_state.code, state.code_);
                goto get_receipt;
            }
            else {
                goto rerun;
            }

        get_receipt:
            MONAD_LOG_INFO(block_logger, "Merged {}", index);
            fibers[index].join();
            all_txn_gas_reward += TTraits::calculate_txn_award(
                b.transactions[index],
                b.header.base_fee_per_gas.value_or(0),
                result.gas_used);
            r.push_back(result);
            ++index;
            continue;

        rerun:
            MONAD_LOG_INFO(block_logger, "Re-running {}...", index);
            TxnProcData new_run{
                db,
                block_state,
                b.transactions[index],
                b.header,
                block_cache,
                index};
            new_run();
            auto &new_result = new_run.result_;
            {
                std::shared_lock<TMutex> const lock{block_state.mutex};
                MONAD_DEBUG_ASSERT(
                    can_merge(block_state.state, new_result.second.state_));
                merge(block_state.state, new_result.second.state_);
                merge(block_state.code, new_result.second.code_);
            }
            fibers[index].join();
            all_txn_gas_reward += TTraits::calculate_txn_award(
                b.transactions[index],
                b.header.base_fee_per_gas.value_or(0),
                new_result.first.gas_used);
            r.push_back(new_result.first);
            ++index;
        }

        // Process withdrawls
        TTraits::process_withdrawal(
            block_state, db, block_cache, b.withdrawals);

        // Apply block reward to beneficiary
        TTraits::apply_block_award(
            block_state, db, block_cache, b, all_txn_gas_reward);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        MONAD_LOG_INFO(
            block_logger,
            "Finish executing Block {}, time elapsed = {}",
            b.header.number,
            elapsed_ms);
        MONAD_LOG_DEBUG(block_logger, "Receipts: {}", r);

        commit(block_state, db);

        return r;
    }

    template <class TMutex>
    void commit(BlockState<TMutex> &block_state, Db &db)
    {
        auto *block_logger = log::logger_t::get_logger("block_logger");
        auto const start_time = std::chrono::steady_clock::now();
        MONAD_LOG_INFO(block_logger, {}, "Committing to DB...");

        db.commit(block_state.state, block_state.code);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        MONAD_LOG_INFO(
            block_logger, "Finished committing, time elapsed = {}", elapsed_ms);
    }
};

MONAD_EXECUTION_NAMESPACE_END
