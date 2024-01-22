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
struct Db;

template <evmc_revision rev>
Result<std::vector<Receipt>>
execute_block(Block &, Db &, BlockHashBuffer const &, fiber::PriorityPool &);

MONAD_NAMESPACE_END
