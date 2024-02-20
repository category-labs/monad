#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct Receipt;
struct Transaction;

template <evmc_revision rev>
Result<Receipt> execute_impl(
    uint64_t i, Transaction const &, Address const &sender, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

template <evmc_revision rev>
Result<Receipt> execute(
    uint64_t i, Transaction const &, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

MONAD_NAMESPACE_END
