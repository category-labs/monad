#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>

#include <monad/db/db.hpp>

#include <monad/execution/block_reward.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

MONAD_NAMESPACE_BEGIN

void apply_block_reward(
    BlockState &block_state, Db &db, Block const &block,
    uint256_t const &block_reward, uint256_t const &ommer_reward)
{
    State state{block_state, db};
    auto const miner_reward =
        calculate_block_reward(block, block_reward, ommer_reward);

    // reward block beneficiary, YP Eqn. 172
    if (MONAD_LIKELY(miner_reward)) {
        state.add_to_balance(block.header.beneficiary, miner_reward);
    }

    // reward ommers, YP Eqn. 175
    for (auto const &header : block.ommers) {
        auto const ommer_reward =
            calculate_ommer_reward(block, block_reward, header.number);
        if (MONAD_LIKELY(ommer_reward)) {
            state.add_to_balance(header.beneficiary, ommer_reward);
        }
    }
    MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
    merge(block_state.state, state.state_);
}

MONAD_NAMESPACE_END
