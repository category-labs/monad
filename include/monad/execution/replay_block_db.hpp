#pragma once

#include <monad/core/block.hpp>

#include <monad/db/block_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/ethereum/genesis.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/logging/monad_log.hpp>

#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <fstream>
#include <optional>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, class TBlockDb, class TExecution,
    template <typename> class TAllTxnBlockProcessor, class TTransactionTrie,
    class TReceiptTrie, class TReceiptCollector>
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
        DECODE_BLOCK_ERROR,
        WRONG_STATE_ROOT,
        WRONG_TRANSACTIONS_ROOT,
        WRONG_RECEIPTS_ROOT
    };

    struct Result
    {
        Status status;
        block_num_t block_number;
    };

    template <concepts::fork_traits<typename TState::ChangeSet> TTraits>
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

    [[nodiscard]] bool verify_root_hash(
        BlockHeader const &block_header, bytes32_t transactions_root,
        bytes32_t receipts_root, bytes32_t const state_root,
        block_num_t current_block_number) const
    {
        auto *block_logger = log::logger_t::get_logger("block_logger");

        MONAD_LOG_INFO(block_logger, "Block {}", current_block_number);

        MONAD_LOG_INFO(
            block_logger,
            "Computed Transaction Root: {}, Expected Transaction Root: "
            "{}",
            transactions_root,
            block_header.transactions_root);
        MONAD_LOG_INFO(
            block_logger,
            "Computed Receipt Root: {}, Expected Receipt Root: {}",
            receipts_root,
            block_header.receipts_root);
        MONAD_LOG_INFO(
            block_logger,
            "Computed State Root: {}, Expected State Root: {}",
            state_root,
            block_header.state_root);

        // TODO: only check for state root hash for now (we don't have receipt
        // and transaction trie building algo yet)
        return state_root == block_header.state_root;
    }

    template <
        concepts::fork_traits<typename TState::ChangeSet> TTraits,
        template <typename, typename> class TTxnProcessor,
        template <typename, typename, typename, typename> class TEvm,
        template <typename, typename, typename> class TStaticPrecompiles,
        template <typename, typename, typename> class TEvmHost,
        template <typename, typename, typename, typename> class TFiberData,
        class TInterpreter, class TPrecompiles>
    [[nodiscard]] Result run_fork(
        TState &state, TBlockDb &block_db, TReceiptCollector &receipt_collector,
        block_num_t current_block_number,
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

                // TODO: Do we need to support functionality to specify genesis
                // file location?
                if (current_block_number == 0u &&
                    TTraits::last_block_number == 1'149'999u) { // genesis block
                    auto const genesis_file_path =
                        test_resource::ethereum_genesis_dir / "mainnet.json";

                    [[maybe_unused]] auto const block_header =
                        ethereum::read_genesis(
                            genesis_file_path, state.accounts_.db_);
                }

                TAllTxnBlockProcessor<TExecution> block_processor{};
                auto const receipts = block_processor.template execute<
                    TState,
                    TTraits,
                    TFiberData<
                        TState,
                        TTxnProcessor<typename TState::ChangeSet, TTraits>,
                        TEvmHost<
                            typename TState::ChangeSet,
                            TTraits,
                            TEvm<
                                typename TState::ChangeSet,
                                TTraits,
                                TStaticPrecompiles<
                                    typename TState::ChangeSet,
                                    TTraits,
                                    TPrecompiles>,
                                TInterpreter>>,
                        TExecution>>(state, block);

                state.commit();

                // TODO: How exactly do we calculate transaction root and
                // receipt root?
                TTransactionTrie transaction_trie(block.transactions);
                TReceiptTrie receipt_trie(receipts);

                auto const transactions_root = transaction_trie.root_hash();
                auto const receipts_root = receipt_trie.root_hash();

                if (!verify_root_hash(
                        block.header,
                        transactions_root,
                        receipts_root,
                        state.get_state_hash(),
                        current_block_number)) {
                    return Result{
                        Status::WRONG_STATE_ROOT, current_block_number - 1u};
                }
                else {
                    state.create_and_prune_block_history(current_block_number);
                }

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
                TInterpreter,
                TPrecompiles>(
                state,
                block_db,
                receipt_collector,
                current_block_number,
                until_block_number);
        }
    }

    template <
        concepts::fork_traits<typename TState::ChangeSet> TTraits,
        template <typename, typename> class TTxnProcessor,
        template <typename, typename, typename, typename> class TEvm,
        template <typename, typename, typename> class TStaticPrecompiles,
        template <typename, typename, typename> class TEvmHost,
        template <typename, typename, typename, typename> class TFiberData,
        class TInterpreter, class TPrecompiles>
    [[nodiscard]] Result
    run(TState &state, TBlockDb &block_db, TReceiptCollector &receipt_collector,
        block_num_t start_block_number,
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
            TInterpreter,
            TPrecompiles>(
            state,
            block_db,
            receipt_collector,
            start_block_number,
            until_block_number);
    }
};

MONAD_EXECUTION_NAMESPACE_END
