#pragma once

#include <monad/core/block.hpp>

#include <monad/db/block_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/ethereum/genesis.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/logging/formatter.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <fstream>
#include <optional>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TDb, class TMutex, class TBlockDb, class TBlockProcessor>
class ReplayFromBlockDb
{
public:
    using state_t = state::State<TMutex, TBlockDb>;

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

    template <class TTraits>
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
        BlockHeader const &block_header, bytes32_t /* transactions_root */,
        bytes32_t /* receipts_root */, bytes32_t const state_root,
        block_num_t /*current_block_number */) const
    {
        LOG_INFO(
            "Computed State Root: {}, Expected State Root: {}",
            state_root,
            block_header.state_root);

        // TODO: only check for state root hash for now (we don't have receipt
        // and transaction trie building algo yet)
        return state_root == block_header.state_root;
    }

    template <
        class TTraits, template <typename, typename> class TTxnProcessor,
        template <typename, typename> class TEvm,
        template <typename, typename> class TEvmHost,
        template <typename, typename, typename, typename> class TFiberData>
    [[nodiscard]] Result run_fork(
        TDb &db, uint64_t const checkpoint_frequency, TBlockDb &block_db,
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

                TTraits::validate_block(block);

                TBlockProcessor block_processor{};
                auto const receipts = block_processor.template execute<
                    TMutex,
                    TTraits,
                    TFiberData<
                        TMutex,
                        TTxnProcessor<state_t, TTraits>,
                        TEvmHost<state_t, TTraits>,
                        TBlockDb>>(block, db, block_db);

                if (!verify_root_hash(
                        block.header,
                        NULL_ROOT,
                        NULL_ROOT,
                        db.state_root(),
                        current_block_number)) {
                    return Result{
                        Status::WRONG_STATE_ROOT, current_block_number - 1u};
                }
                else {
                    if (current_block_number % checkpoint_frequency == 0) {
                        db.create_and_prune_block_history(current_block_number);
                    }
                    block_db.store_current_block_hash(current_block_number);
                }
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
                TEvmHost,
                TFiberData>(
                db,
                checkpoint_frequency,
                block_db,
                current_block_number,
                until_block_number);
        }
    }

    template <
        class TTraits, template <typename, typename> class TTxnProcessor,
        template <typename, typename> class TEvm,
        template <typename, typename> class TEvmHost,
        template <typename, typename, typename, typename> class TFiberData>
    [[nodiscard]] Result
    run(TDb &db, uint64_t const checkpoint_frequency, TBlockDb &block_db,
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

        return run_fork<TTraits, TTxnProcessor, TEvm, TEvmHost, TFiberData>(
            db,
            checkpoint_frequency,
            block_db,
            start_block_number,
            until_block_number);
    }
};

MONAD_EXECUTION_NAMESPACE_END
