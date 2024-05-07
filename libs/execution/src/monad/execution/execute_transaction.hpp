#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

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

template <evmc_revision rev>
evmc::Result execute_impl_no_validation(
    State &state, EvmcHost<rev> &host, Transaction const &tx,
    Address const &sender, uint256_t const &base_fee_per_gas,
    Address const &beneficiary);

template <evmc_revision rev>
Result<Receipt> execute_impl(
    Chain const &, uint64_t i, Transaction const &, Address const &sender,
    BlockHeader const &, BlockHashBuffer const &, BlockState &,
    boost::fibers::promise<void> &prev);

template <evmc_revision rev>
Result<Receipt> execute(
    Chain const &, uint64_t i, Transaction const &, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

MONAD_NAMESPACE_END
