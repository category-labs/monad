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

#include <category/core/event/event_ring.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#include <monad/test/config.hpp>

#include <vector>

MONAD_TEST_NAMESPACE_BEGIN

// Smart pointer to an execution event whose payload stays resident in event
// ring memory
template <typename T>
struct RingEvent
{
    monad_event_descriptor event;
    T const *payload;
    monad_event_ring const *event_ring;

    explicit operator bool() const
    {
        return event_ring != nullptr &&
               monad_event_ring_payload_check(event_ring, &event);
    }

    T const *operator->() const
    {
        return static_cast<bool>(*this) ? payload : nullptr;
    }
};

// Captured execution events in a block; we don't capture everything, because
// the tests don't have enough information to check most of it (no call frames,
// etc.)
struct ExecutionEvents
{
    RingEvent<monad_exec_block_start> block_start;
    RingEvent<monad_exec_block_end> block_end;
    RingEvent<monad_exec_block_reject> block_reject_code;
    RingEvent<monad_exec_txn_reject> txn_reject_code;
    std::vector<RingEvent<monad_exec_txn_header_start>> txn_inputs;
    std::vector<RingEvent<monad_exec_txn_evm_output>> txn_evm_outputs;
};

// After a block is executed, iterate through the recorded events and
// populate the ExecutionEvents structure with any events discovered
void find_execution_events(
    monad_event_ring const *, monad_event_iterator *, ExecutionEvents *);

void init_exec_event_recorder();

MONAD_TEST_NAMESPACE_END
