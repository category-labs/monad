#pragma once

#include <monad/config.hpp>
#include <monad/event/event_emitter.hpp>
#include <monad/event/execution_event.h>

MONAD_NAMESPACE_BEGIN

class ReplayEventEmitter : public EventEmitter
{
    uint64_t block_num_;
    monad_execution_event_type next_state_;

public:
    ReplayEventEmitter(uint64_t start_block = 1);

    std::optional<Event> next_event() override;
};

MONAD_NAMESPACE_END
