#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockState;
struct Block;
struct Chain;
struct ExecutionResult;
struct MonadConsensusBlockHeader;

namespace fiber
{
    class PriorityPool;
}

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &, MonadConsensusBlockHeader const &, Block &, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &);

Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &, evmc_revision, MonadConsensusBlockHeader const &, Block &,
    BlockState &, BlockHashBuffer const &, fiber::PriorityPool &);

MONAD_NAMESPACE_END
