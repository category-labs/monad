#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockMetrics;
class BlockState;
struct Chain;
struct Receipt;
struct Transaction;

template <evmc_revision rev>
struct EvmcHost;

struct ExecutionResult
{
    State state;
    Receipt receipt;
    std::vector<CallFrame> call_frames;
};

uint64_t g_star(
    evmc_revision, Transaction const &, uint64_t gas_remaining,
    uint64_t refund);

template <evmc_revision rev>
evmc::Result execute_impl_no_validation(
    State &state, EvmcHost<rev> &host, Transaction const &tx,
    Address const &sender, uint256_t const &base_fee_per_gas,
    Address const &beneficiary, uint64_t max_code_size);

template <evmc_revision rev>
Result<ExecutionResult> execute(
    Chain const &, uint64_t i, Transaction const &, Address const &,
    BlockHeader const &, BlockHashBuffer const &, BlockState &, BlockMetrics &,
    boost::fibers::promise<void> &prev);

MONAD_NAMESPACE_END
