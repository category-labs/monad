#pragma once

#include <monad/core/block.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/stats/stats.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

enum class TxnReadyStatus
{
    WILL_SUCCEED,
    POSSIBLY_SUCCEED,
    ERROR,
};

template <
    class TState, concepts::fork_traits<TState> TTraits, class TTxnProcessor,
    class TEvm, class TExecution, class TStatsWriter>
struct alignas(64) TransactionProcessorFiberData
{
    using txn_processor_status_t = typename TTxnProcessor::Status;

    TState &s_;
    Transaction const &txn_;
    BlockHeader const &bh_;
    int id_;
    Receipt result_{};
    stats::BlockStats &block_stats_;

    TransactionProcessorFiberData(
        TState &s, Transaction const &t, BlockHeader const &b, int id,
        stats::BlockStats &bs)
        : s_{s}
        , txn_{t}
        , bh_{b}
        , id_{id}
        , result_{.status = 1u, .gas_used = txn_.gas_limit}
        , block_stats_{bs}
    // TODO: should we charge for gas on validation failure? #54
    {
    }

    // this is an injectable policy?
    static constexpr inline TxnReadyStatus
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

    inline Receipt get_receipt() const noexcept { return result_; }

    inline void validate_execute_and_apply_state_diff()
    {
        TStatsWriter::start_txn(block_stats_, id_);
        TTxnProcessor p{};

        while (true) { // retry until apply state cleanly
            while (true) { // spin until *could be* successful
                auto const status = is_valid(
                    p.validate(s_, txn_, bh_.base_fee_per_gas.value_or(0)));
                if (status == TxnReadyStatus::WILL_SUCCEED) {
                    break;
                }
                else if (
                    (s_.current_txn() == id_ &&
                     status != TxnReadyStatus::WILL_SUCCEED) ||
                    status == TxnReadyStatus::ERROR) {
                    // TODO: Charge for validation failure? #54
                    return;
                }
                TExecution::yield();
            }

            auto txn_state = s_.get_copy();
            TEvm e{};
            result_ = p.execute(txn_state, e, bh_, txn_);

            if (auto const applied = s_.apply_state(txn_state); applied) {
                TStatsWriter::finish_txn(block_stats_, id_);
                // whenever a txn is executed successfully,
                // we take a snapshot of block_stats, this
                // could be changed
                TStatsWriter::take_snapshot(block_stats_);
                return;
            }

            // should be re-starting, but the detail is handled in TStatsWriter
            // class
            TStatsWriter::start_txn(block_stats_, id_);
            TExecution::yield();
        }
    }

    inline void operator()() // required signature for boost::fibers
    {
        validate_execute_and_apply_state_diff();
    }
};

MONAD_EXECUTION_NAMESPACE_END
