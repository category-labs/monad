#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct Receipt;
struct Transaction;

template <evmc_revision rev>
Result<Receipt> execute_impl(
    Transaction const &, Address const &sender, BlockHeader const &,
    BlockHashBuffer const &, BlockState &, boost::fibers::promise<void> &prev);

template <evmc_revision rev>
void execute(
    unsigned i, std::shared_ptr<std::optional<Result<Receipt>>[]>,
    std::shared_ptr<boost::fibers::promise<void>[]>, Transaction const &,
    BlockHeader const &, BlockHashBuffer const &, BlockState &);

MONAD_NAMESPACE_END
