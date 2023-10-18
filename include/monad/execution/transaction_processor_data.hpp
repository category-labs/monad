#pragma once

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/db/db.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

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
    BlockState<TMutex> &bs_;
    Transaction const &txn_;
    BlockHeader const &bh_;
    BlockHashBuffer const &block_hash_buffer_;
    unsigned id_;
    result_t result_;

    TransactionProcessorFiberData(
        Db &db, BlockState<TMutex> &bs, Transaction &t, BlockHeader const &bh,
        BlockHashBuffer const &block_hash_buffer, unsigned int id)
        : db_{db}
        , bs_{bs}
        , txn_{t}
        , bh_{bh}
        , block_hash_buffer_{block_hash_buffer}
        , id_{id}
        , result_{
              Receipt{
                  .status = Receipt::Status::FAILED,
                  .gas_used = txn_.gas_limit},
              state::State{bs_, db_}}
    {
    }

    static constexpr bool is_valid(TransactionStatus status) noexcept
    {
        if (status == TransactionStatus::SUCCESS) {
            return true;
        }
        return false;
    }

    void validate_and_execute()
    {
        auto &state = result_.second;
        TTxnProcessor p{};

        auto const start_time = std::chrono::steady_clock::now();
        LOG_INFO(
            "Start executing Transaction {}, from = {}, to = {}",
            id_,
            txn_.from,
            txn_.to);

        auto validity =
            p.static_validate(txn_, bh_.base_fee_per_gas.value_or(0));
        if (validity == TransactionStatus::SUCCESS) {
            validity = p.validate(state, txn_);
        }
        if (!is_valid(validity)) {
            LOG_INFO(
                "Transaction {} invalid: {}", id_, static_cast<int>(validity));
            // TODO: Issue #164, Issue #54
            return;
        }

        TEvmHost host{block_hash_buffer_, bh_, txn_, state};
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
        LOG_INFO(
            "Finish executing Transaction {}, time elapsed = {}",
            id_,
            elapsed_ms);
    }
};

MONAD_EXECUTION_NAMESPACE_END
