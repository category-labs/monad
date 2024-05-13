#pragma once

#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/config.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/result.hpp>
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

#include <boost/outcome/try.hpp>

#include <quill/Quill.h>

#include <cstdint>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

class ReplayFromBlockDb
{
public:
    uint64_t n_transactions{0};

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

    Result<uint64_t> run_fork(
        Db &db, BlockDb &block_db, BlockHashBuffer &block_hash_buffer,
        fiber::PriorityPool &priority_pool, uint64_t const start_block_number,
        uint64_t const nblocks)
    {
        MONAD_ASSERT(start_block_number);

        EthereumMainnet const chain{};

        uint64_t i = 0;
        for (; i < nblocks; ++i) {
            uint64_t const block_number = start_block_number + i;
            if (MONAD_UNLIKELY(!block_number)) {
                break; // wrapped
            }

            Block block{};
            if (!block_db.get(block_number, block)) {
                return i;
            }

            block_hash_buffer.set(block_number - 1, block.header.parent_hash);

            {
                auto result = chain.static_validate_header(block.header);
                if (MONAD_UNLIKELY(result.has_error())) {
                    LOG_ERROR(
                        "block {} {}",
                        block.header.number,
                        result.assume_error().message().c_str());
                    return std::move(result).assume_error();
                }
            }

            evmc_revision const rev = chain.get_revision(block.header);

            BOOST_OUTCOME_TRY(static_validate_block(rev, block));

            BlockState block_state(db);
            BOOST_OUTCOME_TRY(
                auto const receipts,
                execute_block(
                    rev, block, block_state, block_hash_buffer, priority_pool));
            BOOST_OUTCOME_TRY(validate_header(receipts, block.header));
            block_state.log_debug();
            block_state.commit(receipts);

            n_transactions += block.transactions.size();

            if (!verify_root_hash(
                    rev,
                    block.header,
                    NULL_ROOT,
                    db.receipts_root(),
                    db.state_root())) {
                return BlockError::WrongStateRoot;
            }
        }

        return i;
    }

    Result<uint64_t>
    run(Db &db, BlockDb &block_db, fiber::PriorityPool &priority_pool,
        uint64_t const start_block_number, uint64_t const nblocks)
    {
        Block block{};

        BlockHashBuffer block_hash_buffer;
        uint64_t block_number =
            start_block_number < 256 ? 1 : start_block_number - 255;
        for (; block_number < start_block_number; ++block_number) {
            block = Block{};
            bool const result = block_db.get(block_number, block);
            MONAD_ASSERT(result);
            block_hash_buffer.set(block_number - 1, block.header.parent_hash);
        }

        return run_fork(
            db,
            block_db,
            block_hash_buffer,
            priority_pool,
            start_block_number,
            nblocks);
    }
};

MONAD_NAMESPACE_END
