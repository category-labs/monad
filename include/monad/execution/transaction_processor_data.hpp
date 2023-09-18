#pragma once

#include <monad/core/block.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/db/db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/logging/formatter.hpp>

#include <monad/state2/state.hpp>

#include <quill/Quill.h>

#include <chrono>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TMutex, class TTxnProcessor, class TEvmHost, class TBlockCache>
struct alignas(64) TransactionProcessorFiberData
{
    using txn_processor_status_t = typename TTxnProcessor::Status;
    using state_t = state::State<TMutex, TBlockCache>;

    state_t state_;
    Transaction const &txn_;
    BlockHeader const &bh_;
    unsigned int id_;
    Receipt result_;

    TransactionProcessorFiberData(
        Db &db, BlockState<TMutex> &bs, Transaction &t, BlockHeader const &b,
        TBlockCache &block_cache, unsigned int id)
        : state_{bs, db, block_cache}
        , txn_{t}
        , bh_{b}
        , id_{id}
        , result_{.status = Receipt::Status::FAILED, .gas_used = txn_.gas_limit}
    {
    }

    static constexpr bool is_valid(txn_processor_status_t status) noexcept
    {
        if (status == txn_processor_status_t::SUCCESS) {
            return true;
        }
        return false;
    }

    Receipt get_receipt() const noexcept { return result_; }
    state_t &get_state() noexcept { return state_; }

    void validate_and_execute()
    {
        TTxnProcessor p{};

        [[maybe_unused]] auto const start_time =
            std::chrono::steady_clock::now();
        QUILL_LOG_INFO(
            quill::get_logger("txn_logger"),
            "Start executing Transaction {}, from = {}, to = {}",
            id_,
            txn_.from,
            txn_.to);

        auto const validity =
            p.validate(state_, txn_, bh_.base_fee_per_gas.value_or(0));
        if (!is_valid(validity)) {
            QUILL_LOG_INFO(
                quill::get_logger("txn_logger"),
                "Transaction {} invalid: {}",
                id_,
                std::to_underlying(validity));
            // TODO: Issue #164, Issue #54
            return;
        }

        TEvmHost host{bh_, txn_, state_};
        result_ = p.execute(
            state_,
            host,
            txn_,
            bh_.base_fee_per_gas.value_or(0),
            bh_.beneficiary);

        QUILL_LOG_INFO(
            quill::get_logger("txn_logger"),
            "Finish executing Transaction {}, time elapsed = {}",
            id_,
            std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start_time));
    }

    void operator()() // required signature for boost::fibers
    {
        validate_and_execute();
    }
};

MONAD_EXECUTION_NAMESPACE_END
