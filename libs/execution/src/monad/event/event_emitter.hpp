#pragma once

#include <monad/config.hpp>
#include <monad/event/execution_event.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct EventEmitter
{
    struct Event
    {
        monad_execution_event_type kind;
        std::string filename;
    };

    virtual std::optional<Event> next_event() = 0;
    virtual ~EventEmitter() = default;
};

MONAD_NAMESPACE_END
