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

evmc::Result execute_impl_no_validation(
    evmc_revision, BlockHashBuffer const &, BlockHeader const &,
    uint256_t const &chain_id, State &, Transaction const &,
    Address const &sender);

Receipt execute_final(
    evmc_revision, State &, Transaction const &, Address const &sender,
    uint256_t const &base_fee_per_gas, evmc::Result const &,
    Address const &beneficiary);

template <evmc_revision rev>
Result<Receipt> execute_impl(
    Chain &, uint64_t i, Transaction const &, Address const &sender,
    BlockHeader const &, BlockHashBuffer const &, BlockState &,
    boost::fibers::promise<void> &prev);

template <evmc_revision rev>
Result<Receipt> execute(
    Chain &, uint64_t i, Transaction const &, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

MONAD_NAMESPACE_END
