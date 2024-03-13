#pragma once

#define PREFETCH 1
#define PREEXEC 0
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/result.hpp>
#if PREEXEC
#include <monad/state3/state.hpp>
#endif

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct Receipt;
struct Transaction;

#if PREEXEC
template <evmc_revision rev>
Result<evmc::Result> execute_impl2(
    Transaction const &tx, Address const &sender, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, State &state);
#endif

template <evmc_revision rev>
Result<Receipt> execute_impl(
    uint64_t i, Transaction const &, Address const &sender, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

template <evmc_revision rev>
Result<Receipt> execute(
    uint64_t i, Transaction const &, BlockHeader const &,
#if PREFETCH
    std::optional<Address> const &,
#endif
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

MONAD_NAMESPACE_END
