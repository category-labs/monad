#include "runloop_monad.hpp"
#include "util.hpp"

#include <monad/chain/chain.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <optional>
#include <thread>

namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN

namespace
{

    std::optional<Block>
    read_block(fs::path const &ledger_dir, uint64_t const i)
    {
        auto const path = ledger_dir / std::to_string(i);
        if (!fs::exists(path)) {
            return std::nullopt;
        }
        MONAD_ASSERT(fs::is_regular_file(path));
        std::ifstream istream(path);
        if (!istream) {
            LOG_ERROR_LIMIT(
                std::chrono::seconds(30),
                "Opening {} failed with {}",
                path,
                strerror(errno));
            return std::nullopt;
        }
        std::ostringstream buf;
        buf << istream.rdbuf();
        auto view = byte_string_view{
            (unsigned char *)buf.view().data(), buf.view().size()};
        auto block_result = rlp::decode_block(view);
        if (block_result.has_error()) {
            return std::nullopt;
        }
        MONAD_ASSERT(view.empty());
        return block_result.assume_value();
    }
}

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    Chain const &chain, std::filesystem::path const &ledger_dir, Db &db,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &block_num,
    uint64_t const nblocks, sig_atomic_t const volatile &stop)
{
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);

    uint64_t const batch_size =
        nblocks == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;

    uint64_t const end_block_num =
        (std::numeric_limits<uint64_t>::max() - block_num + 1) <= nblocks
            ? std::numeric_limits<uint64_t>::max()
            : block_num + nblocks - 1;
    uint64_t const init_block_num = block_num;
    while (block_num <= end_block_num && stop == 0) {
        auto opt_block = read_block(ledger_dir, block_num);
        if (!opt_block.has_value()) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }
        auto &block = opt_block.value();

        BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

        evmc_revision const rev =
            chain.get_revision(block.header.number, block.header.timestamp);

        BOOST_OUTCOME_TRY(static_validate_block(rev, block));

        // Ethereum: always execute off of the parent proposal round, commit to
        // `round = block_number`, and finalize immediately after that.
        // TODO: get round number from event emitter
        db.set_block_and_round(
            block.header.number - 1,
            (block.header.number == init_block_num)
                ? std::nullopt
                : std::make_optional(block.header.number - 1));
        BlockState block_state(db);
        BOOST_OUTCOME_TRY(
            auto const results,
            execute_block(
                chain,
                rev,
                block,
                block_state,
                block_hash_buffer,
                priority_pool));

        std::vector<Receipt> receipts(results.size());
        std::vector<std::vector<CallFrame>> call_frames(results.size());
        std::vector<Address> senders(results.size());
        for (unsigned i = 0; i < results.size(); ++i) {
            auto &result = results[i];
            receipts[i] = std::move(result.receipt);
            call_frames[i] = (std::move(result.call_frames));
            senders[i] = result.sender;
        }

        block_state.log_debug();
        block_state.commit(
            MonadConsensusBlockHeader::from_eth_header(
                block.header), // TODO: remove when we parse consensus blocks
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
