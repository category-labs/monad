#pragma once

#include <monad/config.hpp>
#include <monad/db/block_db.hpp>
#include <monad/emitter/block_emitter.hpp>
#include <monad/emitter/execution_event.h>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

class ReplayEmitter : public BlockEmitter
{
    BlockDb block_db_;
    uint64_t block_num_;
    Action next_state_;

public:
    ReplayEmitter(std::filesystem::path const &, uint64_t start_block = 1);

    std::optional<std::pair<Action, ConsensusBlock>> next_block() override;
};

MONAD_NAMESPACE_END
