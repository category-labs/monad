#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/event/replay_event_emitter.hpp>

MONAD_NAMESPACE_BEGIN

ReplayEventEmitter::ReplayEventEmitter(uint64_t start_block)
    : block_num_{start_block}
    , next_state_{MONAD_PROPOSE_BLOCK}
{
}

std::optional<ReplayEventEmitter::Event> ReplayEventEmitter::next_event()
{
    auto const state = next_state_;
    Event ev;
    switch (state) {
    case MONAD_PROPOSE_BLOCK:
        next_state_ = MONAD_FINALIZE_BLOCK;
        ev.kind = state;
        ev.filename = std::to_string(block_num_);
        break;
    case MONAD_FINALIZE_BLOCK:
        next_state_ = MONAD_VERIFY_BLOCK;
        ev.kind = state;
        ev.filename = std::to_string(block_num_);
        break;
    default:
        next_state_ = MONAD_PROPOSE_BLOCK;
        ev.kind = state;
        ev.filename = std::to_string(block_num_);
        ++block_num_;
    }
    return ev;
}

MONAD_NAMESPACE_END
