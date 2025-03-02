#pragma once

#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.h>

#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockMetrics;
class BlockState;
struct Chain;
struct ExecutionResult;

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, std::span<Address const> senders, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &, BlockMetrics &,
    std::span<boost::fibers::promise<void>> txn_record_sync_barriers);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, std::span<Address const> senders,
    BlockState &, BlockHashBuffer const &, fiber::PriorityPool &,
    BlockMetrics &,
    std::span<boost::fibers::promise<void>> txn_record_sync_barriers);

std::vector<std::optional<Address>> recover_senders(
    std::span<Transaction const>, fiber::PriorityPool &,
    std::span<boost::fibers::promise<void>> txn_record_sync_barriers);

MONAD_NAMESPACE_END
