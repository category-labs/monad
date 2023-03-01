#include <monad/execution/execution.hpp>

#include <monad/db/buffer.hpp>

#include <silkworm/common/assert.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/execution/processor.hpp>

namespace silkworm::stagedsync {

StageResult MonadExecution::run(db::RWTxn& txn, monad::BlockDb const &block_db, db::MonadBuffer &buffer, silkworm::BlockNum block_num) {
    assert(block_num == db::stages::read_stage_progress(*txn, db::stages::kExecutionKey) + 1);
    static constexpr size_t kCacheSize{5'000};
    BaselineAnalysisCache analysis_cache{kCacheSize};
    ObjectPool<EvmoneExecutionState> state_pool;

    std::vector<Receipt> receipts;

    Block block{};
    if (!silkworm::db::read_block_by_number(block_db, block_num, false, block)) {
        throw std::runtime_error("Unable to read block " + std::to_string(block_num));
    }
    if (block.header.number != block_num) {
        throw std::runtime_error("Bad block sequence");
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
    db::stages::write_stage_progress(*txn, db::stages::kExecutionKey, block_num);
    return StageResult::kSuccess;
}

}  // namespace silkworm::stagedsync
