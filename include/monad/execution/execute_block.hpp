#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct DbRW;

template <evmc_revision rev>
Result<std::vector<Receipt>>
execute_block(Block &, DbRW &, BlockHashBuffer const &, fiber::PriorityPool &);

Result<std::vector<Receipt>> execute_block(
    evmc_revision, Block &, DbRW &, BlockHashBuffer const &,
    fiber::PriorityPool &);

MONAD_NAMESPACE_END
