#include <monad/execution/flush.hpp>

#include <monad/db/buffer.hpp>

namespace silkworm::stagedsync {

StageResult MonadFlush::run(db::RWTxn& txn, [[maybe_unused]] monad::BlockDb const &block_db, db::MonadBuffer &buffer, [[maybe_unused]] silkworm::BlockNum block_num) {
    buffer.write_to_db();
    txn.commit();
    return StageResult::kSuccess;
}

}  // namespace silkworm::stagedsync
