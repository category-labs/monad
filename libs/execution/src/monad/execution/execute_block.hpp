#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.h>

#include <atomic>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct ExecutionResult;

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, std::span<Address const> senders, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &,
    std::span<boost::fibers::promise<void>> txn_record_sync_barriers);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, std::span<Address const> senders,
    BlockState &, BlockHashBuffer const &, fiber::PriorityPool &,
    std::span<boost::fibers::promise<void>> txn_record_sync_barriers);

std::vector<std::optional<Address>> recover_senders(
    std::span<Transaction const>, fiber::PriorityPool &,
    std::span<boost::fibers::promise<void>> txn_record_sync_barriers);

MONAD_NAMESPACE_END
