#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/emitter/execution_event.h>

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

struct BlockEmitter
{
    enum class Action
    {
        EXECUTE,
        FINALIZE,
    };
    virtual std::optional<std::pair<Action, ConsensusBlock>> next_block() = 0;
    virtual ~BlockEmitter() = default;
};

MONAD_NAMESPACE_END
