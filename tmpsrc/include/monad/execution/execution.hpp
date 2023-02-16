#pragma once

#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>

#include <silkworm/consensus/engine.hpp>
#include <silkworm/execution/analysis_cache.hpp>
#include <silkworm/execution/evm.hpp>
#include <silkworm/stagedsync/common.hpp>

namespace silkworm::stagedsync {

class MonadExecution final : public IStage {
  public:
    explicit MonadExecution(NodeSettings* node_settings)
        : IStage(db::stages::kExecutionKey, node_settings),
          block_db_{node_settings->data_directory->block_db().path()},
          state_db_{node_settings->data_directory->state_db().path()},
          consensus_engine_{consensus::engine_factory(node_settings->chain_config.value())} {}

    ~MonadExecution() override = default;

    StageResult forward(db::RWTxn& txn) final;

    std::vector<std::string> get_log_progress() final;

  private:
    monad::BlockDb const block_db_;
    monad::StateDb state_db_;

    std::unique_ptr<consensus::IEngine> consensus_engine_;
};

}  // namespace silkworm::stagedsync
