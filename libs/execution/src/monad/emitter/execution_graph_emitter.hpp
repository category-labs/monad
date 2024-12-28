#pragma once

#include <monad/config.hpp>
#include <monad/emitter/block_emitter.hpp>

#include <deque>
#include <filesystem>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

class ExecutionGraphEmitter : public BlockEmitter
{
    uint64_t last_finalized_round_;
    uint64_t last_proposed_round_;
    std::filesystem::path ledger_dir_;
    mpt::Db &db_;
    std::deque<ConsensusBlockHeader> to_execute_{};
    std::deque<ConsensusBlockHeader> to_execute_optimistic_{};

    bool has_executed(ConsensusBlockHeader const &) const;
    void populate_chain(
        std::string_view, std::deque<ConsensusBlockHeader> &, uint64_t);
    std::pair<Action, ConsensusBlock> pop_execute();
    std::pair<Action, ConsensusBlock> pop_optimistic_execute();

public:
    ExecutionGraphEmitter(uint64_t, std::filesystem::path const &, mpt::Db &);

    std::optional<std::pair<Action, ConsensusBlock>> next_block() override;
};

MONAD_NAMESPACE_END
