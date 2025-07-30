// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/assert.h>
#include <category/core/event/event_metadata.h>
#include <category/core/event/event_ring.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>

#include <quill/Quill.h>

#include <memory>
#include <string_view>
#include <utility>

#include <errno.h>
#include <string.h>
#include <unistd.h>

MONAD_NAMESPACE_BEGIN

ExecutionEventRecorder::ExecutionEventRecorder(
    int ring_fd, std::string_view ring_path, monad_event_ring const &exec_ring)
    : exec_recorder_{}
    , exec_ring_{exec_ring}
    , block_start_seqno_{0}
    , ring_path_{ring_path}
    , ring_fd_{dup(ring_fd)}
{
    MONAD_ASSERT_PRINTF(
        ring_fd_ != -1,
        "dup(2) of ring_fd failed: %s (%d)",
        strerror(errno),
        errno);
    int const rc = monad_event_ring_init_recorder(&exec_ring_, &exec_recorder_);
    MONAD_ASSERT_PRINTF(
        rc == 0, "init recorder failed: %s", monad_event_ring_get_last_error());
}

ExecutionEventRecorder::~ExecutionEventRecorder()
{
    unlink(ring_path_.c_str());
    (void)close(ring_fd_);
    monad_event_ring_unmap(&exec_ring_);
}

void ExecutionEventRecorder::diagnose_reserve_failure(
    monad_exec_event_type type, size_t payload_size) const
{
    // This indicates a giant (> UINT32_MAX) event payload reservation failure;
    // in practice, this means either malicious activity or an EVM bug, whereby
    // the creation of unrealistically large execution outputs is possible.
    // In normal operation we would expect gas limits to prevent this; we log
    // the occurance, but the event will be lost entirely
    monad_event_metadata const &md =
        g_monad_exec_event_metadata[std::to_underlying(type)];

    LOG_ERROR(
        "Ignored {} [{}] event because payload size {} was too large",
        md.c_name,
        std::to_underlying(type),
        payload_size);
}

std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

MONAD_NAMESPACE_END
