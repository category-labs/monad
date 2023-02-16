#include <monad/execution/execution.hpp>

#include <span>
#include <string>

#include <silkworm/common/assert.hpp>
#include <silkworm/common/endian.hpp>
#include <silkworm/common/log.hpp>
#include <silkworm/common/stopwatch.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/db/buffer.hpp>
#include <silkworm/execution/processor.hpp>

namespace silkworm::stagedsync {

StageResult MonadExecution::forward(db::RWTxn& txn) {
    auto block_num{get_progress(txn) + 1};
    static constexpr size_t kCacheSize{5'000};
    BaselineAnalysisCache analysis_cache{kCacheSize};
    ObjectPool<EvmoneExecutionState> state_pool;

    db::Buffer buffer(block_db_, state_db_, *txn, 0);
    std::vector<Receipt> receipts;

    Block block{};
    if (!db::read_block_by_number(block_db_, block_num, false, block)) {
        throw std::runtime_error("Unable to read block " + std::to_string(block_num));
    }
    if (block.header.number != block_num) {
        throw std::runtime_error("Bad block sequence");
    }

    if ((block_num % 64 == 0) && is_stopping()) {
        return StageResult::kAborted;
    }

    ExecutionProcessor processor(block, *consensus_engine_, buffer, node_settings_->chain_config.value());
    processor.evm().baseline_analysis_cache = &analysis_cache;
    processor.evm().state_pool = &state_pool;

    if (const auto res{processor.execute_and_write_block(receipts)}; res != ValidationResult::kOk) {
        const auto block_hash_hex{to_hex(block.header.hash().bytes, true)};
        log::Error("Block Validation Error",
                    {"block", std::to_string(block_num), "hash", block_hash_hex, "err",
                    std::string(magic_enum::enum_name<ValidationResult>(res))});
        return StageResult::kInvalidBlock;
    }

    buffer.insert_receipts(block_num, receipts);
    buffer.write_to_db();

    db::stages::write_stage_progress(*txn, db::stages::kExecutionKey, block_num);

    txn.commit();
    return is_stopping() ? StageResult::kAborted : StageResult::kSuccess;
}

// glee: removed in next commit
std::vector<std::string> MonadExecution::get_log_progress() { return {}; }

}  // namespace silkworm::stagedsync
