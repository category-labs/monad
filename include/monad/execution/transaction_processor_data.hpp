#pragma once

#include <monad/core/block.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/logging/monad_log.hpp>

#include <chrono>

MONAD_EXECUTION_NAMESPACE_BEGIN

enum class TxnReadyStatus
{
    WILL_SUCCEED,
    POSSIBLY_SUCCEED,
    ERROR,
};

template <class TState, class TTxnProcessor, class TEvmHost, class TExecution>
struct alignas(64) TransactionProcessorFiberData
{
    using txn_processor_status_t = typename TTxnProcessor::Status;

    TState &s_;
    Transaction &txn_;
    BlockHeader const &bh_;
    unsigned int id_;
    Receipt result_{};

    TransactionProcessorFiberData(
        TState &s, Transaction &t, BlockHeader const &b, unsigned int id)
        : s_{s}
        , txn_{t}
        , bh_{b}
        , id_{id}
        , result_{.status = 1u, .gas_used = txn_.gas_limit}
    // TODO: should we charge for gas on validation failure? #54
    {
    }

    // this is an injectable policy?
    static constexpr TxnReadyStatus
    is_valid(txn_processor_status_t status) noexcept
    {
        if (status == txn_processor_status_t::SUCCESS) {
            return TxnReadyStatus::WILL_SUCCEED;
        }
        else if (status == txn_processor_status_t::LATER_NONCE) {
            return TxnReadyStatus::POSSIBLY_SUCCEED;
        }
        return TxnReadyStatus::ERROR;
    }

    Receipt get_receipt() const noexcept { return result_; }

    void validate_execute_and_apply_state_diff()
    {
        TTxnProcessor p{};
        auto *txn_logger = log::logger_t::get_logger("txn_logger");
        auto const start_time = std::chrono::steady_clock::now();

        txn_.from = recover_sender(txn_);

        MONAD_LOG_INFO(
            txn_logger,
            "Start executing Transaction {}, from = {}, to = {}",
            id_,
            txn_.from,
            txn_.to);

        while (true) { // retry until apply state cleanly
            // TODO: Issue #164
            auto working_copy = s_.get_working_copy(id_);
            while (true) { // spin until *could be* successful
                auto const status = is_valid(p.validate(
                    working_copy, txn_, bh_.base_fee_per_gas.value_or(0)));
                if (status == TxnReadyStatus::WILL_SUCCEED) {
                    break;
                }
                else if (
                    (s_.current_txn() == id_ &&
                     status != TxnReadyStatus::WILL_SUCCEED) ||
                    status == TxnReadyStatus::ERROR) {

                    MONAD_LOG_INFO(txn_logger, "Transaction {} failed!", id_);
                    // TODO: Charge for validation failure? #54
                    return;
                }
                TExecution::yield();
            }

            TEvmHost host{bh_, txn_, working_copy};
            result_ = p.execute(working_copy, host, bh_, txn_);

            if (s_.can_merge_changes(working_copy) ==
                TState::MergeStatus::WILL_SUCCEED) {
                // apply_state -> can_merge_changes
                // Can merge needs to be in yield while loop while receiving
                // TRY_AGAIN When WILL_SUCCEED is returned, merge, and return;
                // if ERROR is received, then error out
                auto const finished_time = std::chrono::steady_clock::now();
                auto const elapsed_ms =
                    std::chrono::duration_cast<std::chrono::milliseconds>(
                        finished_time - start_time);
                MONAD_LOG_INFO(
                    txn_logger,
                    "Finish executing Transaction {}, time elapsed = {}",
                    id_,
                    elapsed_ms);

                s_.merge_changes(working_copy);
                return;
            }
            MONAD_LOG_INFO(txn_logger, "Transaction {} rescheduled", id_);
            TExecution::yield();
        }
    }

    void operator()() // required signature for boost::fibers
    {
        validate_execute_and_apply_state_diff();
    }
};

MONAD_EXECUTION_NAMESPACE_END
