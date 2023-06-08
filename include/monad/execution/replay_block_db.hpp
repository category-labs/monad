#pragma once

#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/logging/monad_log.hpp>

#include <optional>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, class TBlockDb, class TExecution,
    template <typename> class TAllTxnBlockProcessor,
    template <typename> class TStateTrie, class TTransactionTrie,
    class TReceiptTrie, class TReceiptCollector, class TLogger>
class ReplayFromBlockDb
{
public:
    enum class Status
    {
        SUCCESS_END_OF_DB,
        SUCCESS,
        INVALID_END_BLOCK_NUMBER,
        START_BLOCK_NUMBER_OUTSIDE_DB,
        DECOMPRESS_BLOCK_ERROR,
        DECODE_BLOCK_ERROR
    };

    struct Result
    {
        Status status;
        block_num_t block_number;
    };

    template <concepts::fork_traits<TState> TTraits>
    [[nodiscard]] constexpr block_num_t
    loop_until(std::optional<block_num_t> until_block_number)
    {
        if (!until_block_number.has_value()) {
            return TTraits::last_block_number;
        }
        else {
            return std::min(
                until_block_number.value() - 1u,
                static_cast<uint64_t>(TTraits::last_block_number));
        }
    }

    template <
        concepts::fork_traits<TState> TTraits,
        template <typename, typename> class TTxnProcessor,
        template <typename, typename, typename> class TEvm,
        template <typename, typename, typename> class TStaticPrecompiles,
        template <typename, typename, typename> class TEvmHost,
        template <typename, typename, typename, typename, typename>
        class TFiberData,
        class TPrecompiles>
    [[nodiscard]] Result run_fork(
        TState &state, TStateTrie<TState> &state_trie, TBlockDb const &block_db,
        TReceiptCollector &receipt_collector, block_num_t current_block_number,
        std::optional<block_num_t> until_block_number = std::nullopt)
    {
        for (; current_block_number <= loop_until<TTraits>(until_block_number);
             ++current_block_number) {
            Block block{};
            auto const block_read_status =
                block_db.get(current_block_number, block);

            switch (block_read_status) {
            case TBlockDb::Status::NO_BLOCK_FOUND:
                return Result{
                    Status::SUCCESS_END_OF_DB, current_block_number - 1u};
            case TBlockDb::Status::DECOMPRESS_ERROR:
                return Result{
                    Status::DECOMPRESS_BLOCK_ERROR, current_block_number};
            case TBlockDb::Status::DECODE_ERROR:
                return Result{Status::DECODE_BLOCK_ERROR, current_block_number};
            case TBlockDb::Status::SUCCESS: {
                TAllTxnBlockProcessor<TExecution> block_processor{};
                auto const receipts = block_processor.template execute<
                    TState,
                    TFiberData<
                        TState,
                        TTraits,
                        TTxnProcessor<TState, TTraits>,
                        TEvmHost<
                            TState,
                            TTraits,
                            Evm<TState,
                                TTraits,
                                TStaticPrecompiles<
                                    TState,
                                    TTraits,
                                    TPrecompiles>>>,
                        TExecution>>(state, block);

                TTransactionTrie transaction_trie(block.transactions);
                TReceiptTrie receipt_trie(receipts);

                auto *block_logger = TLogger::get_logger("block_logger");

                [[maybe_unused]] auto const transaction_root =
                    transaction_trie.root_hash();
                [[maybe_unused]] auto const receipt_root =
                    receipt_trie.root_hash();
                [[maybe_unused]] auto const state_root =
                    state_trie.incremental_update(state);

                MONAD_LOG_INFO(block_logger, "Block {}", current_block_number);

                MONAD_LOG_INFO(
                    block_logger,
                    "Computed Transaction Root: {}, Expected Transaction Root: "
                    "{}",
                    transaction_root,
                    block.header.transactions_root);
                MONAD_LOG_INFO(
                    block_logger,
                    "Computed Receipt Root: {}, Expected Receipt Root: {}",
                    receipt_root,
                    block.header.receipts_root);
                MONAD_LOG_INFO(
                    block_logger,
                    "Computed State Root: {}, Expected State Root: {}",
                    state_root,
                    block.header.state_root);

                receipt_collector.emplace_back(receipts);
            }
            default:
                break;
            }
        }

        if (until_block_number.has_value() &&
            until_block_number.value() <= current_block_number) {
            return Result{Status::SUCCESS, current_block_number - 1u};
        }

        else {
            return run_fork<
                typename TTraits::next_fork_t,
                TTxnProcessor,
                TEvm,
                TStaticPrecompiles,
                TEvmHost,
                TFiberData,
                TPrecompiles>(
                state,
                state_trie,
                block_db,
                receipt_collector,
                current_block_number,
                until_block_number);
        }
    }

    template <
        concepts::fork_traits<TState> TTraits,
        template <typename, typename> class TTxnProcessor,
        template <typename, typename, typename> class TEvm,
        template <typename, typename, typename> class TStaticPrecompiles,
        template <typename, typename, typename> class TEvmHost,
        template <typename, typename, typename, typename, typename>
        class TFiberData,
        class TPrecompiles>
    [[nodiscard]] inline Result
    run(TState &state, TStateTrie<TState> &state_trie, TBlockDb const &block_db,
        TReceiptCollector &receipt_collector, block_num_t start_block_number,
        std::optional<block_num_t> until_block_number = std::nullopt)
    {
        Block block{};

        if (until_block_number.has_value() &&
            (until_block_number <= start_block_number)) {
            return Result{Status::INVALID_END_BLOCK_NUMBER, start_block_number};
        }

        if (block_db.get(start_block_number, block) ==
            TBlockDb::Status::NO_BLOCK_FOUND) {
            return Result{
                Status::START_BLOCK_NUMBER_OUTSIDE_DB, start_block_number};
        }

        return run_fork<
            TTraits,
            TTxnProcessor,
            TEvm,
            TStaticPrecompiles,
            TEvmHost,
            TFiberData,
            TPrecompiles>(
            state,
            state_trie,
            block_db,
            receipt_collector,
            start_block_number,
            until_block_number);
    }
};

MONAD_EXECUTION_NAMESPACE_END
