#pragma once

#include <monad/core/block.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

enum class TxnReadyStatus
{
    WILL_SUCCEED,
    POSSIBLY_SUCCEED,
    ERROR,
};

template <
    class TState, concepts::fork_traits<TState> TTraits, class TTxnProcessor,
    class TEvm, class TExecution>
struct alignas(64) TransactionProcessorFiberData
{
    using txn_processor_status_t = typename TTxnProcessor::Status;

    TState &s_;
    Transaction const &txn_;
    BlockHeader const &bh_;
    int id_;
    Receipt result_{};

    TransactionProcessorFiberData(
        TState &s, Transaction const &t, BlockHeader const &b, int id)
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
            TEvm
                e{}; // e needs to be constructed with the working copy of state
            result_ = p.execute(txn_state, e, bh_, txn_);

            if (auto const applied = s_.apply_state(txn_state); applied) {
                // apply_state -> can_merge_changes
                // Can merge needs to be in yield while loop while receiving
                // TRY_AGAIN When WILL_SUCCEED is returned, merge, and return;
                // if ERROR is received, then error out
                return;
            }
            TExecution::yield();
        }
    }

    void operator()() // required signature for boost::fibers
    {
        validate_execute_and_apply_state_diff();
    }
};

MONAD_EXECUTION_NAMESPACE_END
