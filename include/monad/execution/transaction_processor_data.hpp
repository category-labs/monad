#pragma once

#include <monad/config.hpp>

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/db/db.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validation_status.hpp>

#include <monad/state2/state.hpp>

#include <quill/Quill.h>

#include <chrono>

MONAD_NAMESPACE_BEGIN

struct TransactionProcessorFiberData
{
    using result_t = std::pair<Receipt, State>;

    Db &db_;
    BlockState &block_state_;
    Transaction const &txn_;
    BlockHeader const &header_;
    BlockHashBuffer const &block_hash_buffer_;
    unsigned id_;
    result_t result_;

    TransactionProcessorFiberData(
        Db &db, BlockState &block_state, Transaction &txn,
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
              State{block_state_, db_}}
    {
    }

    template <class Traits>
    ValidationStatus validate_and_execute()
    {
        MONAD_DEBUG_ASSERT(
            static_validate_txn<Traits>(txn_, header_.base_fee_per_gas) ==
            ValidationStatus::SUCCESS);

        auto &state = result_.second;
        TransactionProcessor<Traits> processor{};

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

        auto const tx_context = get_tx_context<Traits>(txn_, header_);
        EvmcHost<Traits> host{tx_context, block_hash_buffer_, state};
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

MONAD_NAMESPACE_END
