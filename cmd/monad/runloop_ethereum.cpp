#include "runloop_ethereum.hpp"

#include <monad/chain/chain.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>

#include <algorithm>
#include <chrono>

MONAD_NAMESPACE_BEGIN

namespace
{

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

    void log_tps(
        uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
        uint64_t const gas, std::chrono::steady_clock::time_point const begin)
    {
        auto const now = std::chrono::steady_clock::now();
        auto const elapsed = std::max(
            static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::microseconds>(
                    now - begin)
                    .count()),
            1UL); // for the unlikely case that elapsed < 1 mic
        uint64_t const tps = (ntxs) * 1'000'000 / elapsed;
        uint64_t const gps = gas / elapsed;

        LOG_INFO(
            "Run {:4d} blocks to {:8d}, number of transactions {:6d}, "
            "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
            nblocks,
            block_num,
            ntxs,
            tps,
            gps,
            monad_procfs_self_resident() / (1L << 20));
    };

#pragma GCC diagnostic pop

}

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &chain, std::filesystem::path const &ledger_dir, Db &db,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    uint64_t const batch_size =
        end_block_num == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;

    uint64_t const start_block_num = block_num;
    BlockDb block_db(ledger_dir);
    while (block_num <= end_block_num && stop == 0) {
        Block block;
        MONAD_ASSERT_PRINTF(
            block_db.get(block_num, block),
            "Could not query %lu from blockdb",
            block_num);

        BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

        evmc_revision const rev =
            chain.get_revision(block.header.number, block.header.timestamp);

        BOOST_OUTCOME_TRY(static_validate_block(rev, block));

        auto const recovered_senders =
            recover_senders(block.transactions, priority_pool);
        std::vector<Address> senders(block.transactions.size());
        for (unsigned i = 0; i < recovered_senders.size(); ++i) {
            if (recovered_senders[i].has_value()) {
                senders[i] = recovered_senders[i].value();
            }
            else {
                return TransactionError::MissingSender;
            }
        }
        // Ethereum: always execute off of the parent proposal round, commit to
        // `round = block_number`, and finalize immediately after that.
        db.set_block_and_round(
            block.header.number - 1,
            (block.header.number == start_block_num)
                ? std::nullopt
                : std::make_optional(block.header.number - 1));
        BlockState block_state(db);
        BOOST_OUTCOME_TRY(
            auto results,
            execute_block(
                chain,
                rev,
                block,
                senders,
                block_state,
                block_hash_buffer,
                priority_pool));

        std::vector<Receipt> receipts(results.size());
        std::vector<std::vector<CallFrame>> call_frames(results.size());
        for (unsigned i = 0; i < results.size(); ++i) {
            auto &result = results[i];
            receipts[i] = std::move(result.receipt);
            call_frames[i] = (std::move(result.call_frames));
        }

        block_state.log_debug();
        block_state.commit(
            MonadConsensusBlockHeader::from_eth_header(block.header),
            receipts,
            call_frames,
            senders,
            block.transactions,
            block.ommers,
            block.withdrawals);
        auto const output_header = db.read_eth_header();
        BOOST_OUTCOME_TRY(
            chain.validate_output_header(block.header, output_header));

        db.finalize(block.header.number, block.header.number);
        db.update_verified_block(block.header.number);

        auto const h =
            to_bytes(keccak256(rlp::encode_block_header(output_header)));
        block_hash_buffer.set(block_num, h);

        ntxs += block.transactions.size();
        batch_num_txs += block.transactions.size();
        total_gas += block.header.gas_used;
        batch_gas += block.header.gas_used;
        ++batch_num_blocks;

        if (block_num % batch_size == 0) {
            log_tps(
                block_num,
                batch_num_blocks,
                batch_num_txs,
                batch_gas,
                batch_begin);
            batch_num_blocks = 0;
            batch_num_txs = 0;
            batch_gas = 0;
            batch_begin = std::chrono::steady_clock::now();
        }
        ++block_num;
    }
    if (batch_num_blocks > 0) {
        log_tps(
            block_num, batch_num_blocks, batch_num_txs, batch_gas, batch_begin);
    }
    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
