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

#pragma once

/**
 * @file
 *
 * This file defines the execution event recorder, which is a global object.
 * It is up to the driver code using this library to configure it, otherwise
 * recording will remain disabled.
 */

#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_recorder.hpp>
#include <category/core/event/owned_event_ring.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <utility>

MONAD_NAMESPACE_BEGIN

/// All execution event recording goes through this class; it extends the
/// EventRecorder C++ utility and also keeps track of the block flow ID -- the
/// sequence number of the BLOCK_START event, copied into all subsequent
/// block-level events
class ExecutionEventRecorder : private EventRecorder
{
public:
    using EventRecorder::EventRecorder;

    /// Reserve resources to record a BLOCK_START event; also sets the
    /// current block flow ID
    [[nodiscard]] ReservedEvent<monad_exec_block_start>
    reserve_block_start_event();

    /// Reserve resources to record an event that occurs at block scope
    template <typename T, std::same_as<std::span<std::byte const>>... U>
    [[nodiscard]] ReservedEvent<T>
    reserve_block_event(monad_exec_event_type, U...);

    /// Reserve resources to record a transaction-level event
    template <typename T, std::same_as<std::span<std::byte const>>... U>
    [[nodiscard]] ReservedEvent<T> reserve_txn_event(
        monad_exec_event_type event_type, uint32_t txn_num,
        U &&...trailing_bufs)
    {
        auto r = reserve_block_event<T>(
            event_type, std::forward<U>(trailing_bufs)...);
        r.event->content_ext[MONAD_FLOW_TXN_ID] = txn_num + 1;
        return r;
    }

    /// Mark that the current block has ended
    void end_current_block();

    /// Record a block-level event with no payload in one step
    uint64_t record_block_marker_event(monad_exec_event_type);

    /// Record a transaction-level event with no payload in one step
    uint64_t record_txn_marker_event(monad_exec_event_type, uint32_t txn_num);

    using EventRecorder::commit;

private:
    uint64_t cur_block_start_seqno_;
};

inline ReservedEvent<monad_exec_block_start>
ExecutionEventRecorder::reserve_block_start_event()
{
    ReservedEvent const block_start =
        reserve_block_event<monad_exec_block_start>(MONAD_EXEC_BLOCK_START);
    cur_block_start_seqno_ = block_start.seqno;
    block_start.event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = block_start.seqno;
    return block_start;
}

template <typename T, std::same_as<std::span<std::byte const>>... U>
ReservedEvent<T> ExecutionEventRecorder::reserve_block_event(
    monad_exec_event_type event_type, U... trailing_bufs)
{
    ReservedEvent const r =
        this->reserve_event<T>(event_type, std::forward<U>(trailing_bufs)...);

    // TODO(ken): remove the memset(3) below if the C++ standard evolves
    //
    // Both the C23 and C++20 standards specify that an initialization of the
    // form `S s = {}` will zero-initialize the entire bit representation of
    // the aggregate `S`, including padding bits. As of C23 and C++26, neither
    // specifies what happens to the padding bits if any designated
    // initializers are present. Designated initializers in aggregates is
    // how the memory of `payload_buf` is usually initialized and the execution
    // events ABI requires all padding bits to be zeroed.
    //
    // 1. As an extension, clang-20 and later always explicitly zero-initialize
    //    padding bits, but only in C23 and not C++, see:
    //    https://clang.llvm.org/docs/LanguageExtensions.html#union-and-aggregate-initialization-in-c
    //    https://github.com/llvm/llvm-project/commit/7a086e1b2dc05f54afae3591614feede727601fa
    //
    // 2. In gcc, zero-init of padding bits can be guaranteed in both languages,
    //    in all contexts, via -fzero-init-padding-bits=all; this is both
    //    too heavy-handed and doesn't work in clang++
    //
    // If at some point, the clang C extension behavior becomes standard, then
    // the below memset(3) can be removed. Because the current function is
    // inlineable, the dead stores created by this memset are eliminated, and
    // it has minimal performance impact.
    memset(static_cast<void *>(r.payload), 0, sizeof(T));
    r.event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = cur_block_start_seqno_;
    r.event->content_ext[MONAD_FLOW_TXN_ID] = 0;
    r.event->content_ext[MONAD_FLOW_ACCOUNT_INDEX] = 0;
    return r;
}

inline void ExecutionEventRecorder::end_current_block()
{
    cur_block_start_seqno_ = 0;
}

inline uint64_t ExecutionEventRecorder::record_block_marker_event(
    monad_exec_event_type event_type)
{
    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event =
        monad_event_recorder_reserve(&recorder_, 0, &seqno, &payload_buf);
    event->event_type = std::to_underlying(event_type);
    event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = cur_block_start_seqno_;
    event->content_ext[MONAD_FLOW_TXN_ID] = 0;
    event->content_ext[MONAD_FLOW_ACCOUNT_INDEX] = 0;
    monad_event_recorder_commit(event, seqno);
    return seqno;
}

inline uint64_t ExecutionEventRecorder::record_txn_marker_event(
    monad_exec_event_type event_type, uint32_t txn_num)
{
    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event =
        monad_event_recorder_reserve(&recorder_, 0, &seqno, &payload_buf);
    event->event_type = std::to_underlying(event_type);
    event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = cur_block_start_seqno_;
    event->content_ext[MONAD_FLOW_TXN_ID] = txn_num + 1;
    event->content_ext[MONAD_FLOW_ACCOUNT_INDEX] = 0;
    monad_event_recorder_commit(event, seqno);
    return seqno;
}

// Declare the global event ring and recorder objects; these are initialized by
// the driver process if it wants execution event recording, and are left
// uninitialized to disable it (all internal functions check if they are
// `nullptr` before using them); we use a "straight" global variable rather
// than a "magic static" style singleton, because we don't care as much about
// preventing initialization races as we do about potential cost of poking at
// atomic guard variables every time
extern std::unique_ptr<OwnedEventRing> g_exec_event_ring;
extern std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

/*
 * Helper free functions for execution event recording
 */

inline uint64_t record_block_marker_event(monad_exec_event_type event_type)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record_block_marker_event(event_type);
    }
    return 0;
}

inline uint64_t
record_txn_marker_event(monad_exec_event_type event_type, uint32_t txn_num)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record_txn_marker_event(event_type, txn_num);
    }
    return 0;
}

MONAD_NAMESPACE_END
