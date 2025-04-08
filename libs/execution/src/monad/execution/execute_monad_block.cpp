#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <vector>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &chain, MonadConsensusBlockHeader const &consensus_header,
    Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};
    state.touch(STAKING_CONTRACT_ADDRESS);
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);

    // BOOST_OUTCOME_TRY(contract.reward_validator(consensus_header.author));

    if (consensus_header.epoch != contract.vars.epoch.load()) {
        BOOST_OUTCOME_TRY(
            contract.on_epoch_change()); // TODO: run this on a fiber?
        contract.vars.epoch.store(consensus_header.epoch);
    }
    return execute_block<rev>(
        chain, block, block_state, block_hash_buffer, priority_pool);
}

EXPLICIT_EVMC_REVISION(execute_monad_block);

Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &chain, evmc_revision const rev,
    MonadConsensusBlockHeader const &consensus_header, Block &block,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    SWITCH_EVMC_REVISION(
        execute_monad_block,
        chain,
        consensus_header,
        block,
        block_state,
        block_hash_buffer,
        priority_pool);
    MONAD_ABORT("unreachable");
}

MONAD_NAMESPACE_END
