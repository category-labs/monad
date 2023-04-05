#pragma once

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>
#include <monad/execution/config.hpp>

#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TExecution>
struct IBlockProcessor
{
public:
    template <class TState, class TFiberData>
    [[nodiscard]] std::vector<Receipt>
    execute([[maybe_unused]] TState &state, [[maybe_unused]] Block const &block)
    {
        return {};
    }
};

MONAD_EXECUTION_NAMESPACE_END