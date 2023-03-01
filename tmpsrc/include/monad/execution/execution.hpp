#pragma once

#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>

#include <monad/execution/stage.hpp>

#include <silkworm/consensus/engine.hpp>

namespace silkworm::stagedsync {

class MonadExecution final : public Stage {
  public:
    explicit MonadExecution(NodeSettings* node_settings)
        : Stage(node_settings),
          consensus_engine_{consensus::engine_factory(node_settings->chain_config.value())} {}

    ~MonadExecution() override = default;

    StageResult run(db::RWTxn& txn, monad::BlockDb const &block_db, db::MonadBuffer &buffer, silkworm::BlockNum block_num) final;

  private:
    std::unique_ptr<consensus::IEngine> consensus_engine_;
};

}  // namespace silkworm::stagedsync
