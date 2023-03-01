#pragma once

#include <monad/db/buffer.hpp>

#include <monad/db/block_db.hpp>

#include <silkworm/stagedsync/common.hpp>

namespace silkworm::stagedsync {

class Stage {
  public:
    explicit Stage(NodeSettings* node_settings) : node_settings_{node_settings} {};
    virtual ~Stage() = default;

    [[nodiscard]] virtual StageResult run(db::RWTxn& txn, monad::BlockDb const &block_db, db::MonadBuffer &buffer, BlockNum block_num) = 0;

  protected:
    NodeSettings* node_settings_;
};

}