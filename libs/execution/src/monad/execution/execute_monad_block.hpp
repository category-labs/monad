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

namespace fiber
{
    class PriorityPool;
}

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &, Block &, BlockState &, BlockHashBuffer const &,
    fiber::PriorityPool &);

Result<std::vector<ExecutionResult>> execute_monad_block(
    Chain const &, evmc_revision, Block &, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &);

MONAD_NAMESPACE_END
