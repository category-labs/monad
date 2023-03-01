#pragma once

#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>

#include <monad/execution/stage.hpp>

namespace silkworm::stagedsync {

class MonadFlush final : public Stage {
  public:
    explicit MonadFlush(NodeSettings* node_settings) : Stage(node_settings) {}

    ~MonadFlush() override = default;

    StageResult run(db::RWTxn& txn, monad::BlockDb const &block_db, db::MonadBuffer &buffer, silkworm::BlockNum block_num) final;
};

}  // namespace silkworm::stagedsync
