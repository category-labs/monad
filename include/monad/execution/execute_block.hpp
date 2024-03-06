#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Db;

template <evmc_revision rev>
Result<std::vector<Receipt>>
execute_block(Block &, Db &, BlockHashBuffer const &, fiber::PriorityPool &);

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block_no_post_validate(
    Block &, BlockHashBuffer const &, fiber::PriorityPool &, BlockState &,
    uint64_t &cumulative_gas_used);

MONAD_NAMESPACE_END
