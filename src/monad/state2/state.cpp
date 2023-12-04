#include <monad/config.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas_fmt.hpp>

#include <quill/detail/LogMacros.h>

MONAD_NAMESPACE_BEGIN

void State::log_debug() const
{
    LOG_DEBUG("State Deltas: {}", state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
