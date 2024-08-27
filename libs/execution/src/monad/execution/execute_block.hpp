#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/invoke_rev.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;

template <evmc_revision rev>
struct ExecuteBlock
{
    Result<std::vector<Receipt>> operator()(
        Chain const &, Block &, BlockState &, BlockHashBuffer const &,
        fiber::PriorityPool &);
};

MONAD_NAMESPACE_END
