#include <monad/core/assert.h>
#include <monad/core/event/exec_event_ctypes.h>
#include <monad/core/event/exec_event_recorder.hpp>
#include <monad/event/event_ring.h>

#include <atomic>
#include <memory>
#include <string_view>

#include <unistd.h>

MONAD_NAMESPACE_BEGIN

ExecutionEventRecorder::ExecutionEventRecorder(
    int ring_fd, std::string_view ring_path, monad_event_ring const &exec_ring)
    : exec_recorder_{}
    , exec_ring_{exec_ring}
    , block_start_seqno_{0}
    , ring_path_{ring_path}
    , ring_fd_{ring_fd}
    , exiting_{false}
{
    int const rc = monad_event_ring_init_recorder(&exec_ring_, &exec_recorder_);
    MONAD_ASSERT_PRINTF(
        rc == 0, "init recorder failed: %s", monad_event_ring_get_last_error());
}

ExecutionEventRecorder::~ExecutionEventRecorder()
{
    exiting_.store(true, std::memory_order::release);
    unlink(ring_path_.c_str());
    (void)close(ring_fd_);
    monad_event_ring_unmap(&exec_ring_);
}

std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

MONAD_NAMESPACE_END
