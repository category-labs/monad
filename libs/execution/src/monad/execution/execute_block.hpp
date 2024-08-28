#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct Chain;
struct ExecutionResult;

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain &, Block &, BlockState &, BlockHashBuffer const &,
    fiber::PriorityPool &);

Result<std::vector<ExecutionResult>> execute_block(
    Chain &, evmc_revision, Block &, BlockState &, BlockHashBuffer const &,
    fiber::PriorityPool &);

MONAD_NAMESPACE_END
