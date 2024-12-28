#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/emitter/replay_emitter.hpp>

MONAD_NAMESPACE_BEGIN

ReplayEmitter::ReplayEmitter(
    std::filesystem::path const &block_db_path, uint64_t const start_block)
    : block_db_{block_db_path}
    , block_num_{start_block}
    , next_state_{Action::EXECUTE}
{
}

std::optional<std::pair<BlockEmitter::Action, ConsensusBlock>>
ReplayEmitter::next_block()
{
    auto const state = next_state_;
    Block eth_block;
    if (!block_db_.get(block_num_, eth_block)) {
        return std::nullopt;
    }

    ConsensusBlock block{
        .header =
            ConsensusBlockHeader{
                .parent_bft_block_id = {},
                .round = block_num_,
                .parent_round = block_num_ - 1,
                .block_body_id = {},
                .proposed = std::move(eth_block.header),
                .verified_blocks = std::vector<BlockHeader>{}},
        .body = ConsensusBlockBody{
            .transactions = std::move(eth_block.transactions),
            .ommers = std::move(eth_block.ommers),
            .withdrawals = {},
        }};
    if (eth_block.withdrawals.has_value()) {
        block.body.withdrawals = std::move(eth_block.withdrawals.value());
    }
    switch (state) {
    case Action::EXECUTE:
        next_state_ = Action::FINALIZE;
        break;
    case Action::FINALIZE:
        next_state_ = Action::EXECUTE;
        ++block_num_;
        break;
    }
    return std::make_pair(state, block);
}

MONAD_NAMESPACE_END
