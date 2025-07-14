#pragma once

#include <category/core/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/receipt.hpp>
#include <category/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <monad/metrics/block_metrics.hpp>

#include <evmc/evmc.h>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct ExecutionResult;

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, std::vector<Address> const &senders, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &, BlockMetrics &);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, std::vector<Address> const &senders,
    BlockState &, BlockHashBuffer const &, fiber::PriorityPool &,
    BlockMetrics &);

std::vector<std::optional<Address>>
recover_senders(std::vector<Transaction> const &, fiber::PriorityPool &);

MONAD_NAMESPACE_END
