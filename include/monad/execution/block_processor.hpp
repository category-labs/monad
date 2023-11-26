#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/execution/validation_status.hpp>

#include <evmc/evmc.h>

#include <tl/expected.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Db;

template <evmc_revision rev>
tl::expected<std::vector<Receipt>, ValidationStatus>
execute_block(Block &, Db &, BlockHashBuffer const &);

MONAD_NAMESPACE_END
