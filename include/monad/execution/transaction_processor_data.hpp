#pragma once

#include <monad/core/block.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/db/db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/logging/monad_log.hpp>

#include <monad/state2/state.hpp>

#include <chrono>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TMutex, class TTxnProcessor, class TEvmHost, class TBlockCache>
struct TransactionProcessorFiberData
{
    using txn_processor_status_t = typename TTxnProcessor::Status;
    using state_t = state::State<TMutex, TBlockCache>;
    using result_t = std::pair<Receipt, state::State<TMutex, TBlockCache>>;

    Db &db_;
    BlockState<TMutex> &bs_;
    Transaction const &txn_;
    BlockHeader const &bh_;
    TBlockCache &block_cache_;
    unsigned id_;
    result_t result_;

    TransactionProcessorFiberData(
        Db &db, BlockState<TMutex> &bs, Transaction &t, BlockHeader const &bh,
        TBlockCache &block_cache, unsigned int id)
        : db_{db}
        , bs_{bs}
        , txn_{t}
        , bh_{bh}
        , block_cache_{block_cache}
        , id_{id}
        , result_{
              Receipt{
                  .status = Receipt::Status::FAILED,
                  .gas_used = txn_.gas_limit},
              state::State{bs_, db_, block_cache_}}
    {
    }

    result_t &&get_result() noexcept { return std::move(result_); }

    static constexpr bool is_valid(txn_processor_status_t status) noexcept
    {
        if (status == txn_processor_status_t::SUCCESS) {
            return true;
        }
        return false;
    }

    void validate_and_execute()
    {
        auto &state = result_.second;
        TTxnProcessor p{};

        auto *txn_logger = log::logger_t::get_logger("txn_logger");
        auto const start_time = std::chrono::steady_clock::now();
        MONAD_LOG_INFO(
            txn_logger,
            "Start executing Transaction {}, from = {}, to = {}",
            id_,
            txn_.from,
            txn_.to);

        auto const validity =
            p.validate(state, txn_, bh_.base_fee_per_gas.value_or(0));
        if (!is_valid(validity)) {
            MONAD_LOG_INFO(
                txn_logger, "Transaction {} invalid: {}", id_, validity);
            // TODO: Issue #164, Issue #54
            return;
        }

        TEvmHost host{bh_, txn_, state};
        result_.first = p.execute(
            state,
            host,
            txn_,
            bh_.base_fee_per_gas.value_or(0),
            bh_.beneficiary);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        MONAD_LOG_INFO(
            txn_logger,
            "Finish executing Transaction {}, time elapsed = {}",
            id_,
            elapsed_ms);
    }

    // required signature for boost::fibers
    void operator()() { validate_and_execute(); }
};

MONAD_EXECUTION_NAMESPACE_END
