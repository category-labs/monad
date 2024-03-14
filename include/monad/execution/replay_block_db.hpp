#pragma once

#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/config.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>

#include <nlohmann/json.hpp>

#include <quill/Quill.h>

#include <test_resource_data.h>

#include <cstdint>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

class ReplayFromBlockDb
{
public:
    uint64_t n_transactions{0};

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

    bool verify_root_hash(
        evmc_revision const rev, BlockHeader const &block_header,
        bytes32_t /* transactions_root */, bytes32_t const receipts_root,
        bytes32_t const state_root) const
    {
        if (state_root != block_header.state_root) {
            LOG_ERROR(
                "Block: {}, Computed State Root: {}, Expected State Root: {}",
                block_header.number,
                state_root,
                block_header.state_root);
            return false;
        }
        if (MONAD_LIKELY(rev >= EVMC_BYZANTIUM)) {
            if (receipts_root != block_header.receipts_root) {
                LOG_ERROR(
                    "Block: {}, Computed Receipts Root: {}, Expected Receipts "
                    "Root: {}",
                    block_header.number,
                    receipts_root,
                    block_header.receipts_root);
                return false;
            }
        }
        return true;
    }

    Result run_fork(
        Db &db, BlockDb &block_db, BlockHashBuffer &block_hash_buffer,
        fiber::PriorityPool &priority_pool, block_num_t current_block_number,
        std::optional<block_num_t> until_block_number = std::nullopt)
    {
        EthereumMainnet chain{};

        for (; current_block_number <= until_block_number;
             ++current_block_number) {
            Block block{};
            bool const block_read_status =
                block_db.get(current_block_number, block);

            if (MONAD_UNLIKELY(!block_read_status)) {
                return Result{
                    Status::SUCCESS_END_OF_DB, current_block_number - 1};
            }

            block_hash_buffer.set(
                current_block_number - 1, block.header.parent_hash);

            evmc_revision const rev = chain.get_revision(block.header);

            if (auto const result = static_validate_block(rev, block);
                result.has_error()) {
                LOG_ERROR(
                    "Block validation error: {}",
                    result.assume_error().value());
                return Result{
                    Status::BLOCK_VALIDATION_FAILED, current_block_number};
            }

            auto const receipts =
                execute_block(rev, block, db, block_hash_buffer, priority_pool);

            n_transactions += block.transactions.size();

            if (!verify_root_hash(
                    rev,
                    block.header,
                    NULL_ROOT,
                    db.receipts_root(),
                    db.state_root())) {
                return Result{Status::WRONG_STATE_ROOT, current_block_number};
            }
        }

        return Result{Status::SUCCESS, current_block_number - 1};
    }

    Result
    run(Db &db, BlockDb &block_db, fiber::PriorityPool &priority_pool,
        block_num_t const start_block_number,
        std::optional<block_num_t> const until_block_number = std::nullopt)
    {
        Block block{};

        if (until_block_number.has_value() &&
            (until_block_number <= start_block_number)) {
            return Result{Status::INVALID_END_BLOCK_NUMBER, start_block_number};
        }

        if (!block_db.get(start_block_number, block)) {
            return Result{
                Status::START_BLOCK_NUMBER_OUTSIDE_DB, start_block_number};
        }

        BlockHashBuffer block_hash_buffer;
        block_num_t block_number =
            start_block_number < 256 ? 1 : start_block_number - 255;
        while (block_number < start_block_number) {
            block = Block{};
            bool const result = block_db.get(block_number, block);
            MONAD_ASSERT(result);
            block_hash_buffer.set(block_number - 1, block.header.parent_hash);
            ++block_number;
        }

        return run_fork(
            db,
            block_db,
            block_hash_buffer,
            priority_pool,
            start_block_number,
            until_block_number);
    }
};

MONAD_NAMESPACE_END
