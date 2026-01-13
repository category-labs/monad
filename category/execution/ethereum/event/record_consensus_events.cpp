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

#include <category/core/config.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_consensus_events.hpp>

MONAD_NAMESPACE_BEGIN

void record_mock_consensus_events(
    bytes32_t const &block_id, uint64_t block_number)
{
    if (auto *exec_recorder = g_exec_event_recorder.get()) {
        ReservedExecEvent const block_qc =
            exec_recorder->reserve_block_event<monad_exec_block_qc>(
                MONAD_EXEC_BLOCK_QC);
        *block_qc.payload = monad_exec_block_qc{
            .block_tag = {.id = block_id, .block_number = block_number},
            .round = block_number + 1,
            .epoch = 0};
        exec_recorder->commit(block_qc);

        ReservedExecEvent const block_finalized =
            exec_recorder->reserve_block_event<monad_exec_block_finalized>(
                MONAD_EXEC_BLOCK_FINALIZED);
        *block_finalized.payload = monad_exec_block_finalized{
            .id = block_id, .block_number = block_number};
        exec_recorder->commit(block_finalized);

        ReservedExecEvent const block_verified =
            exec_recorder->reserve_block_event<monad_exec_block_verified>(
                MONAD_EXEC_BLOCK_VERIFIED);
        *block_verified.payload =
            monad_exec_block_verified{.block_number = block_number};
        exec_recorder->commit(block_verified);
    }
}

MONAD_NAMESPACE_END
