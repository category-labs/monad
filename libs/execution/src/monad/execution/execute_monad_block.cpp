#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/contract/uint256.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/util.hpp>
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
    Chain const &chain, Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    // TODO: move to validate_monad_block?
    if (MONAD_UNLIKELY(
            block.header.extra_data.size() !=
            sizeof(uint64_t) + sizeof(Address))) {
        return BlockError::MissingField;
    }

    byte_string_view extra_data{block.header.extra_data};
    auto const epoch = intx::be::unsafe::load<uint64_t>(
        extra_data.substr(0, sizeof(uint64_t)).data());
    auto const block_author = unaligned_load<Address>(
        extra_data.substr(sizeof(uint64_t), sizeof(Address)).data());
    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    state.touch(STAKING_CONTRACT_ADDRESS);

    auto const contract_epoch = contract.vars.epoch.load_unchecked().native();
    if (MONAD_UNLIKELY(epoch != contract_epoch)) {
        contract.vars.epoch.store(Uint256Native{epoch}.to_be());
        BOOST_OUTCOME_TRY(contract.syscall_on_epoch_change());
    }
    if (MONAD_UNLIKELY(block_author != Address{})) {
        BOOST_OUTCOME_TRY(contract.syscall_reward_validator(block_author));
    }
    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    std::vector<ExecutionResult> results;
    BOOST_OUTCOME_TRY(
        results,
        execute_block<rev>(
            chain, block, block_state, block_hash_buffer, priority_pool));

    return results;
}

EXPLICIT_EVMC_REVISION(execute_monad_block);

Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &chain, evmc_revision const rev, Block &block,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    SWITCH_EVMC_REVISION(
        execute_monad_block,
        chain,
        block,
        block_state,
        block_hash_buffer,
        priority_pool);
    MONAD_ABORT("unreachable");
}

MONAD_NAMESPACE_END
