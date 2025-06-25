#pragma once

#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct Chain;
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
