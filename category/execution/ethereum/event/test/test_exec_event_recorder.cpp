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
#include <category/core/bytes.hpp>
#include <category/core/cleanup.h>
#include <category/core/config.hpp>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <mutex>
#include <span>
#include <vector>

#include <string.h>
#include <sys/mman.h>

using namespace monad;

namespace
{
    // g_exec_event_recorder is deliberately not a "magic static" to avoid
    // poking at guard variables, since we normally don't care about
    // initialization races; here we do, if the tests want to run in parallel
    std::once_flag recorder_initialized;

    void ensure_recorder_initialized()
    {
        constexpr uint8_t DESCRIPTORS_SHIFT = 20;
        constexpr uint8_t PAYLOAD_BUF_SHIFT = 28; // 256 MiB
        constexpr char MEMFD_NAME[] = "exec_recorder_test";

        int ring_fd [[gnu::cleanup(cleanup_close)]] =
            memfd_create(MEMFD_NAME, 0);
        ASSERT_NE(ring_fd, -1);
        monad_event_ring_simple_config const simple_cfg = {
            .descriptors_shift = DESCRIPTORS_SHIFT,
            .payload_buf_shift = PAYLOAD_BUF_SHIFT,
            .context_large_pages = 0,
            .content_type = MONAD_EVENT_CONTENT_TYPE_EXEC,
            .schema_hash = g_monad_exec_event_schema_hash};
        int rc =
            monad_event_ring_init_simple(&simple_cfg, ring_fd, 0, MEMFD_NAME);
        MONAD_ASSERT_PRINTF(
            rc == 0,
            "event library error -- %s",
            monad_event_ring_get_last_error());

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

        g_exec_event_recorder = std::make_unique<ExecutionEventRecorder>(
            ring_fd, MEMFD_NAME, exec_ring);
    }

} // End of anonymous namespace

TEST(ExecEventRecorder, Basic)
{
    Address const log_address = static_cast<Address>(0x12345678UL);
    bytes32_t const log_topics[] = {
        bytes32_t{0x1}, NULL_HASH, NULL_HASH_BLAKE3};
    constexpr char log_data[] = "Hello world!";
    uint32_t const txn_num = 30;

    std::call_once(recorder_initialized, ensure_recorder_initialized);
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();

    // Note: the subspan(0) calls are there to make the spans into dynamic
    // extent spans, rather than compile-time fixed-sized spans. Normally this
    // API is never given fixed-sized spans, because the trailing buffer
    // variadic args are by definition used for recording variably-sized
    // trailing data. `std::span{x}` evaluates to a fixed-sized span because
    // our testing data has a known extent.
    ReservedExecEvent const log_event =
        exec_recorder->reserve_txn_event<monad_exec_txn_log>(
            MONAD_EXEC_TXN_LOG,
            txn_num,
            as_bytes(std::span{log_topics}).subspan(0),
            as_bytes(std::span{log_data}).subspan(0));
    ASSERT_NE(log_event.event, nullptr);
    ASSERT_NE(log_event.payload, nullptr);
    ASSERT_NE(log_event.seqno, 0);

    *log_event.payload = monad_exec_txn_log{
        .index = 0,
        .address = log_address,
        .topic_count = static_cast<uint8_t>(std::size(log_topics)),
        .data_length = static_cast<uint32_t>(std::size(log_data))};

    exec_recorder->commit(log_event);

    monad_event_descriptor event;
    ASSERT_TRUE(monad_event_ring_try_copy(
        exec_recorder->get_event_ring(), log_event.seqno, &event));
    ASSERT_EQ(event.event_type, MONAD_EXEC_TXN_LOG);
    ASSERT_EQ(event.content_ext[MONAD_FLOW_TXN_ID], txn_num + 1);

    auto const *const written_log = static_cast<monad_exec_txn_log const *>(
        monad_event_ring_payload_peek(exec_recorder->get_event_ring(), &event));
    ASSERT_EQ(memcmp(written_log, log_event.payload, sizeof *written_log), 0);
    ASSERT_EQ(memcmp(written_log + 1, log_topics, sizeof log_topics), 0);
    ASSERT_EQ(
        memcmp(
            reinterpret_cast<std::byte const *>(written_log + 1) +
                sizeof log_topics,
            log_data,
            sizeof log_data),
        0);
}

TEST(ExecEventRecorder, Overflow)
{
    std::vector<uint8_t> truncated;
    Address const log_address = static_cast<Address>(0x12345678UL);
    uint32_t const txn_num = 30;

    // Make some data to put in the truncated buffer region. We will also pass
    // in a giant buffer after this one, to cause the > 4GiB overflow. The
    // giant buffer may not point to valid memory, but because we will have
    // copied up the maximum truncation size from this smaller buffer first,
    // the library won't try to access the giant buffer
    for (unsigned i = 0;
         i < ExecutionEventRecorder::RECORD_ERROR_TRUNCATED_SIZE;
         ++i) {
        truncated.push_back(static_cast<uint8_t>(i));
    }

    std::call_once(recorder_initialized, ensure_recorder_initialized);
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();

    constexpr size_t OverflowSize = 1UL << 32;
    ReservedExecEvent const log_event =
        exec_recorder->reserve_txn_event<monad_exec_txn_log>(
            MONAD_EXEC_TXN_LOG,
            txn_num,
            std::as_bytes(std::span{truncated}),
            std::span{
                reinterpret_cast<std::byte const *>(truncated.data()),
                OverflowSize});
    ASSERT_NE(log_event.event, nullptr);
    ASSERT_NE(log_event.payload, nullptr);
    ASSERT_NE(log_event.seqno, 0);

    // The user will typically not know that error has happened; they will
    // write into the payload area as though this is the real payload, but
    // it's really part of the MONAD_EXEC_RECORD_ERROR layout
    *log_event.payload = monad_exec_txn_log{
        .index = 0,
        .address = log_address,
        .topic_count = 0,
        .data_length = 0,
    };

    exec_recorder->commit(log_event);

    monad_event_descriptor event;
    ASSERT_TRUE(monad_event_ring_try_copy(
        exec_recorder->get_event_ring(), log_event.seqno, &event));
    ASSERT_EQ(event.event_type, MONAD_EXEC_RECORD_ERROR);
    ASSERT_EQ(event.content_ext[MONAD_FLOW_TXN_ID], txn_num + 1);

    size_t const expected_requested_payload_size =
        sizeof(*log_event.payload) + std::size(truncated) + OverflowSize;
    auto const *const written_error =
        static_cast<monad_exec_record_error const *>(
            monad_event_ring_payload_peek(
                exec_recorder->get_event_ring(), &event));

    size_t const expected_truncation_size =
        ExecutionEventRecorder::RECORD_ERROR_TRUNCATED_SIZE -
        sizeof(*written_error);
    ASSERT_EQ(written_error->error_type, MONAD_EVENT_RECORD_ERROR_OVERFLOW_4GB);
    ASSERT_EQ(written_error->dropped_event_type, MONAD_EXEC_TXN_LOG);
    ASSERT_EQ(written_error->truncated_payload_size, expected_truncation_size);
    ASSERT_EQ(
        written_error->requested_payload_size, expected_requested_payload_size);

    // `*log_event.payload` is still copied into the error event, into the
    // truncation area
    ASSERT_EQ(
        memcmp(
            written_error + 1, log_event.payload, sizeof(*log_event.payload)),
        0);

    // Part of the VLT (as much as will fit) is also copied
    size_t const vlt_offset =
        sizeof(*written_error) + sizeof(*log_event.payload);
    ASSERT_EQ(
        memcmp(
            reinterpret_cast<std::byte const *>(written_error) + vlt_offset,
            std::data(truncated),
            written_error->truncated_payload_size - sizeof(*log_event.payload)),
        0);
}
