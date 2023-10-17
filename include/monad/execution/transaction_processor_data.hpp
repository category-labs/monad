#pragma once

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/db/db.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/validation_status.hpp>

#include <monad/state2/state.hpp>

#include <quill/Quill.h>

#include <chrono>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TMutex, class TTxnProcessor, class TEvmHost>
struct TransactionProcessorFiberData
{
    using state_t = state::State<TMutex>;
    using result_t = std::pair<Receipt, state_t>;

    Db &db_;
    BlockState<TMutex> &block_state_;
    Transaction const &txn_;
    BlockHeader const &header_;
    BlockHashBuffer const &block_hash_buffer_;
    unsigned id_;
    result_t result_;

    TransactionProcessorFiberData(
        Db &db, BlockState<TMutex> &block_state, Transaction &txn,
        BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
        unsigned int id)
        : db_{db}
        , block_state_{block_state}
        , txn_{txn}
        , header_{header}
        , block_hash_buffer_{block_hash_buffer}
        , id_{id}
        , result_{
              Receipt{
                  .status = Receipt::Status::FAILED,
                  .gas_used = txn_.gas_limit},
              state::State{block_state_, db_}}
    {
    }

    template <class TTraits>
    ValidationStatus validate_and_execute()
    {
        MONAD_DEBUG_ASSERT(
            static_validate_txn<TTraits>(txn_, header_.base_fee_per_gas) ==
            ValidationStatus::SUCCESS);

        auto &state = result_.second;
        TTxnProcessor processor{};

        auto const start_time = std::chrono::steady_clock::now();
        LOG_INFO(
            "Start executing Transaction {}, from = {}, to = {}",
            id_,
            txn_.from,
            txn_.to);

        if (auto const validity = validate_txn(state, txn_);
            validity != ValidationStatus::SUCCESS) {
            LOG_INFO(
                "Transaction {} invalid: {}", id_, static_cast<int>(validity));
            // TODO: Issue #164, Issue #54
            return validity;
        }

        TEvmHost host{block_hash_buffer_, header_, txn_, state};
        result_.first = processor.execute(
            state,
            host,
            txn_,
            header_.base_fee_per_gas.value_or(0),
            header_.beneficiary);

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        LOG_INFO(
            "Finish executing Transaction {}, time elapsed = {}",
            id_,
            elapsed_ms);

        return ValidationStatus::SUCCESS;
    }
};

MONAD_EXECUTION_NAMESPACE_END
