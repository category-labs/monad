#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/db/config.hpp>

MONAD_DB_NAMESPACE_BEGIN

class IBlockDb
{
public:
    [[nodiscard]] virtual bool
    get(block_num_t block_num, Block &block) const = 0;
};

MONAD_DB_NAMESPACE_END