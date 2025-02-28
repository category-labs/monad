#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_frame.hpp>

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct Chain;
struct Receipt;
class State;
struct Transaction;

template <evmc_revision rev>
struct EvmcHost;

struct ExecutionResult
{
    Receipt receipt;
    Address sender;
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
Result<ExecutionResult> execute_impl(
    Chain const &, uint64_t i, Transaction const &, Address const &sender,
    BlockHeader const &, BlockHashBuffer const &, BlockState &,
    boost::fibers::promise<void> &prev);

template <evmc_revision rev>
Result<ExecutionResult> execute(
    Chain const &, uint64_t i, Transaction const &,
    std::optional<Address> const &, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

MONAD_NAMESPACE_END
