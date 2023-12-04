#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct Receipt;
struct Transaction;

template <evmc_revision rev>
Result<Receipt> execute_impl(
    Transaction &, Address const &sender, BlockHeader const &,
    BlockHashBuffer const &, BlockState &);

template <evmc_revision rev>
Result<Receipt> execute(
    Transaction &, BlockHeader const &, BlockHashBuffer const &, BlockState &);

MONAD_NAMESPACE_END
