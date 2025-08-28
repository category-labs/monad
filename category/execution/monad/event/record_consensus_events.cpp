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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/event/record_consensus_events.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

template <class MonadConsensusBlockHeader>
void record_block_qc(
    MonadConsensusBlockHeader const &header, uint64_t finalized_block_num)
{
    // Before recording a QC for block B, we need to check if that block isn't
    // already finalized. The reason for this check is the following sequence:
    //
    //   - we execute proposed block B1
    //
    //   - execution begins to fall behind, while consensus advances; B1
    //     receives a QC (upon the proposal of B2) and B2 also received a QC
    //     (upon proposal of B3), finalizing B1; the execution daemon is still
    //     working on B1 during this time (or more likely, is restarting after
    //     a crash that occurs immediately after B1 has executed)
    //
    //   - by the time execution is ready to execute another proposed block,
    //     consensus has finalized B1; this is communicated to the execution
    //     daemon, and finalize logic takes precedence and runs immediately,
    //     emitting a BLOCK_FINALIZED event
    //
    //   - during the execution of B2, we'll see the QC for B1. Since it has
    //     already been finalized, we'll skip it
    if (auto *const exec_recorder = g_exec_event_recorder.get()) {
        uint64_t const vote_block_number = header.seqno - 1;
        if (vote_block_number <= finalized_block_num) {
            return;
        }
        auto const &vote = header.qc.vote;
        ReservedExecEvent const block_qc =
            exec_recorder->reserve_block_event<monad_exec_block_qc>(
                MONAD_EXEC_BLOCK_QC);
        *block_qc.payload = monad_exec_block_qc{
            .block_tag = {.id = vote.id, .block_number = vote_block_number},
            .round = vote.round,
            .epoch = vote.epoch};
        exec_recorder->commit(block_qc);
    }
}

#define EXPLICIT_INSTANTIATE_QC_TEMPLATE(HEADER_TYPE) \
template void record_block_qc<HEADER_TYPE>(HEADER_TYPE const &, uint64_t);

EXPLICIT_INSTANTIATE_QC_TEMPLATE(MonadConsensusBlockHeaderV0);
EXPLICIT_INSTANTIATE_QC_TEMPLATE(MonadConsensusBlockHeaderV1);
EXPLICIT_INSTANTIATE_QC_TEMPLATE(MonadConsensusBlockHeaderV2);

#undef EXPLICIT_INSTANTIATE_QC_TEMPLATE

void record_block_finalized(bytes32_t const &block_id, uint64_t block_number)
{
    if (auto *const exec_recorder = g_exec_event_recorder.get()) {
        ReservedExecEvent const block_finalized =
            exec_recorder->reserve_block_event<monad_exec_block_finalized>(
                MONAD_EXEC_BLOCK_FINALIZED);
        *block_finalized.payload = monad_exec_block_finalized{
            .id = block_id, .block_number = block_number};
        exec_recorder->commit(block_finalized);
    }
}

void record_block_verified(std::span<uint64_t const> verified_blocks)
{
    if (auto *const exec_recorder = g_exec_event_recorder.get()) {
        for (uint64_t b : verified_blocks) {
            if (b == 0) {
                continue;
            }
            ReservedExecEvent const block_verified =
                exec_recorder->reserve_block_event<monad_exec_block_verified>(
                    MONAD_EXEC_BLOCK_VERIFIED);
            *block_verified.payload =
                monad_exec_block_verified{.block_number = b};
            exec_recorder->commit(block_verified);
        }
    }
}

MONAD_NAMESPACE_END
