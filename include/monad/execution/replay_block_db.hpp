#pragma once

#include <monad/config.hpp>

#include <monad/core/block.hpp>

#include <monad/db/block_db.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/ethereum/genesis.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execution_model.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

template <class Db>
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
        WRONG_RECEIPTS_ROOT,
        BLOCK_VALIDATION_FAILED,
    };

    struct Result
    {
        Status status;
        block_num_t block_number;
    };

    template <class Traits>
    [[nodiscard]] constexpr block_num_t
    loop_until(std::optional<block_num_t> until_block_number)
    {
        if (!until_block_number.has_value()) {
            return Traits::last_block_number;
        }
        else {
            return std::min(
                until_block_number.value() - 1u,
                static_cast<uint64_t>(Traits::last_block_number));
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

    template <class Traits>
    [[nodiscard]] Result run_fork(
        Db &db, uint64_t const checkpoint_frequency, BlockDb &block_db,
        BlockHashBuffer &block_hash_buffer, block_num_t current_block_number,
        std::optional<block_num_t> until_block_number = std::nullopt)
    {
        for (; current_block_number <= loop_until<Traits>(until_block_number);
             ++current_block_number) {
            Block block{};
            auto const block_read_status =
                block_db.get(current_block_number, block);

            switch (block_read_status) {
            case BlockDb::Status::NO_BLOCK_FOUND:
                return Result{Status::SUCCESS_END_OF_DB, current_block_number};
            case BlockDb::Status::DECOMPRESS_ERROR:
                return Result{
                    Status::DECOMPRESS_BLOCK_ERROR, current_block_number};
            case BlockDb::Status::DECODE_ERROR:
                return Result{Status::DECODE_BLOCK_ERROR, current_block_number};
            case BlockDb::Status::SUCCESS: {

                block_hash_buffer.set(
                    current_block_number - 1, block.header.parent_hash);

                BlockProcessor block_processor{};
                if (auto const status = static_validate_block<Traits>(block);
                    status != ValidationStatus::SUCCESS) {
                    return Result{
                        Status::BLOCK_VALIDATION_FAILED, current_block_number};
                }

                auto const receipts = block_processor.template execute<Traits>(
                    block, db, block_hash_buffer);

                if (!verify_root_hash(
                        block.header,
                        NULL_ROOT,
                        NULL_ROOT,
                        db.state_root(),
                        current_block_number)) {
                    return Result{
                        Status::WRONG_STATE_ROOT, current_block_number};
                }
                else {
                    if (current_block_number % checkpoint_frequency == 0) {
                        db.create_and_prune_block_history(current_block_number);
                    }
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
            return run_fork<typename Traits::next_fork_t>(
                db,
                checkpoint_frequency,
                block_db,
                block_hash_buffer,
                current_block_number,
                until_block_number);
        }
    }

    template <class Traits>
    [[nodiscard]] Result
    run(Db &db, uint64_t const checkpoint_frequency, BlockDb &block_db,
        block_num_t const start_block_number,
        std::optional<block_num_t> const until_block_number = std::nullopt)
    {
        Block block{};

        if (until_block_number.has_value() &&
            (until_block_number <= start_block_number)) {
            return Result{Status::INVALID_END_BLOCK_NUMBER, start_block_number};
        }

        if (block_db.get(start_block_number, block) ==
            BlockDb::Status::NO_BLOCK_FOUND) {
            return Result{
                Status::START_BLOCK_NUMBER_OUTSIDE_DB, start_block_number};
        }

        BlockHashBuffer block_hash_buffer;
        block_num_t block_number =
            start_block_number < 256 ? 1 : start_block_number - 255;
        while (block_number < start_block_number) {
            block = Block{};
            auto const result = block_db.get(block_number, block);
            MONAD_ASSERT(result == BlockDb::Status::SUCCESS);
            block_hash_buffer.set(block_number - 1, block.header.parent_hash);
            ++block_number;
        }

        return run_fork<Traits>(
            db,
            checkpoint_frequency,
            block_db,
            block_hash_buffer,
            start_block_number,
            until_block_number);
    }
};

MONAD_NAMESPACE_END
