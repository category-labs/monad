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

#include <event.hpp>

#include <category/core/assert.h>
#include <category/core/cleanup.h>
#include <category/core/config.hpp>
#include <category/core/event/event_iterator.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>

#include <gtest/gtest.h>
#include <monad/test/config.hpp>

#include <cstdint>
#include <memory>

#include <sys/mman.h>

MONAD_NAMESPACE_BEGIN

// Links against the global object in libmonad_execution_ethereum; remains
// uninitialized if recording is disabled
extern std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

void find_execution_events(
    monad_event_ring const *event_ring, monad_event_iterator *iter,
    ExecutionEvents *exec_events)
{
    monad_event_descriptor event;

ConsumeMore:
    ASSERT_EQ(monad_event_iterator_try_next(iter, &event), MONAD_EVENT_SUCCESS);
    ASSERT_NE(event.event_type, MONAD_EXEC_EVM_ERROR);
    ASSERT_TRUE(monad_event_ring_payload_check(event_ring, &event));
    void const *const payload =
        monad_event_ring_payload_peek(event_ring, &event);

    switch (event.event_type) {
    case MONAD_EXEC_BLOCK_START:
        ASSERT_FALSE(exec_events->block_start);
        exec_events->block_start = {
            event,
            reinterpret_cast<monad_exec_block_start const *>(payload),
            event_ring};
        break;

    case MONAD_EXEC_BLOCK_END:
        ASSERT_FALSE(exec_events->block_end);
        exec_events->block_end = {
            event,
            reinterpret_cast<monad_exec_block_end const *>(payload),
            event_ring};
        return;

    case MONAD_EXEC_BLOCK_REJECT:
        ASSERT_FALSE(exec_events->block_reject_code);
        exec_events->block_reject_code = {
            event,
            reinterpret_cast<monad_exec_block_reject const *>(payload),
            event_ring};
        return;

    case MONAD_EXEC_TXN_REJECT:
        ASSERT_FALSE(exec_events->txn_reject_code);
        exec_events->txn_reject_code = {
            event,
            reinterpret_cast<monad_exec_txn_reject const *>(payload),
            event_ring};
        return;

    case MONAD_EXEC_TXN_HEADER_START:
        exec_events->txn_inputs.emplace_back(
            event,
            reinterpret_cast<monad_exec_txn_header_start const *>(payload),
            event_ring);
        break;

    case MONAD_EXEC_TXN_EVM_OUTPUT:
        exec_events->txn_evm_outputs.emplace_back(
            event,
            reinterpret_cast<monad_exec_txn_evm_output const *>(payload),
            event_ring);
        break;
    }

    // Look for more events until we find the end of the block (either
    // BLOCK_END or one of the other terminating events, e.g. BLOCK_REJECT)
    goto ConsumeMore;
}

void init_exec_event_recorder()
{
    constexpr uint8_t DESCRIPTORS_SHIFT = 20;
    constexpr uint8_t PAYLOAD_BUF_SHIFT = 28; // 256 MiB
    constexpr char MEMFD_NAME[] = "memfd:exec_event_test";

    int ring_fd [[gnu::cleanup(cleanup_close)]] = memfd_create(MEMFD_NAME, 0);
    MONAD_ASSERT(ring_fd != -1);

    // We're the exclusive owner; initialize the event ring file
    monad_event_ring_simple_config const simple_cfg = {
        .descriptors_shift = DESCRIPTORS_SHIFT,
        .payload_buf_shift = PAYLOAD_BUF_SHIFT,
        .context_large_pages = 0,
        .content_type = MONAD_EVENT_CONTENT_TYPE_EXEC,
        .schema_hash = g_monad_exec_event_schema_hash};
    int rc = monad_event_ring_init_simple(&simple_cfg, ring_fd, 0, MEMFD_NAME);
    MONAD_ASSERT_PRINTF(
        rc == 0,
        "event library error -- %s",
        monad_event_ring_get_last_error());

    // mmap the event ring into this process' address space
    monad_event_ring exec_ring;
    rc = monad_event_ring_mmap(
        &exec_ring,
        PROT_READ | PROT_WRITE,
        MAP_POPULATE,
        ring_fd,
        0,
        MEMFD_NAME);
    MONAD_ASSERT_PRINTF(
        rc == 0,
        "event library error -- %s",
        monad_event_ring_get_last_error());

    // Create the execution recorder object
    g_exec_event_recorder = std::make_unique<ExecutionEventRecorder>(
        ring_fd, MEMFD_NAME, exec_ring);
}

MONAD_TEST_NAMESPACE_END
