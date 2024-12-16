#pragma once

#include <monad/config.hpp>
#include <monad/event/event_emitter.hpp>

#include <filesystem>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

class AppendOnlyLogEmitter : public EventEmitter
{
    std::ifstream cursor_;

public:
    AppendOnlyLogEmitter(std::filesystem::path const &);

    std::optional<Event> next_event() override;

    bool rewind_to_event(monad_execution_event const &);
};

MONAD_NAMESPACE_END
