#pragma once

/**
 * @file
 *
 * This file defines the execution event recorder, which is a global object.
 * It is up to the driver code using this library to configure it, otherwise
 * recording will remain disabled.
 */

#include <monad/config.hpp>
#include <monad/core/event/exec_event_ctypes.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_ring.h>

#include <array>
#include <atomic>
#include <bit>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>

#include <string.h>

MONAD_NAMESPACE_BEGIN

class ExecutionEventRecorder
{
public:
    explicit ExecutionEventRecorder(
        int ring_fd, std::string_view ring_path, monad_event_ring const &);

    ~ExecutionEventRecorder();

    uint64_t get_block_start_seqno() const
    {
        return block_start_seqno_;
    }

    uint64_t set_block_start_seqno(uint64_t seqno)
    {
        std::swap(block_start_seqno_, seqno);
        return seqno;
    }

    monad_event_descriptor *
    record_reserve(size_t payload_size, uint64_t *seqno, uint8_t **payload)
    {
        if (exiting_.load(std::memory_order::acquire)) [[unlikely]] {
            return nullptr;
        }
        return monad_event_recorder_reserve(
            &exec_recorder_, payload_size, seqno, payload);
    }

    void record(
        std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
        void const *payload, size_t payload_length)
    {
        if (exiting_.load(std::memory_order::acquire)) [[unlikely]] {
            return;
        }

        uint64_t seqno;
        uint8_t *payload_buf;

        monad_event_descriptor *const event = monad_event_recorder_reserve(
            &exec_recorder_, payload_length, &seqno, &payload_buf);
        if (payload_length > 0) {
            memcpy(payload_buf, payload, payload_length);
        }
        event->event_type = std::to_underlying(type);
        event->user[MONAD_FLOW_BLOCK_SEQNO] = block_start_seqno_;
        event->user[MONAD_FLOW_TXN_ID] = opt_txn_num.value_or(-1) + 1;
        monad_event_recorder_commit(event, seqno);
    }

    void record(std::optional<uint32_t> opt_txn_num, monad_exec_event_type type)
    {
        return record(opt_txn_num, type, nullptr, 0);
    }

    template <typename T>
        requires std::is_trivially_copyable_v<T>
    void record(
        std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
        T const &payload)
    {
        return record(opt_txn_num, type, &payload, sizeof payload);
    }

    template <typename T, std::same_as<std::span<std::byte const>>... U>
        requires std::is_trivially_copyable_v<T>
    void record(
        std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
        T const &payload, U... bufs)
    {
        if (exiting_.load(std::memory_order::acquire)) [[unlikely]] {
            return;
        }

        uint64_t seqno;
        uint8_t *payload_buf;
        size_t const payload_size = (size(bufs) + ... + sizeof payload);

        monad_event_descriptor *const event = monad_event_recorder_reserve(
            &exec_recorder_, payload_size, &seqno, &payload_buf);
        void *p = mempcpy(payload_buf, &payload, sizeof payload);
        ((p = mempcpy(p, data(bufs), size(bufs))), ...);
        event->event_type = std::to_underlying(type);
        event->user[MONAD_FLOW_BLOCK_SEQNO] = block_start_seqno_;
        event->user[MONAD_FLOW_TXN_ID] = opt_txn_num.value_or(-1) + 1;
        monad_event_recorder_commit(event, seqno);
    }

private:
    alignas(64) monad_event_recorder exec_recorder_;
    monad_event_ring exec_ring_;
    uint64_t block_start_seqno_;
    std::string ring_path_;
    int ring_fd_;
    std::atomic<bool> exiting_;
};

// TODO(ken): could use "magic statics" here, but we don't care much about
//    initialization races compared to the potential cost of poking at guard
//    variables every time. Is there a better solution?
extern std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

/// Record an execution event with no payload
inline void record_exec_event(
    std::optional<uint32_t> opt_txn_num, monad_exec_event_type type)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record(opt_txn_num, type);
    }
}

/// Record an execution event whose payload is described by some copyable type T
template <typename T>
    requires std::is_trivially_copyable_v<T>
void record_exec_event(
    std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
    T const &payload)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record(opt_txn_num, type, payload);
    }
}

/// Record an execution event whose payload is described by a copyable type T,
/// followed by a series of runtime-variable length buffers, each described by
/// a `std::span<std::byte const>` (gather I/O). The copyable type T is called
/// a "header event", and will describe the size of the trailing length data
/// to be parsed by the reader (e.g., in transaction logs)
template <typename T, std::same_as<std::span<std::byte const>>... U>
    requires std::is_trivially_copyable_v<T>
void record_exec_event(
    std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
    T const &payload, U &&...bufs)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        e->record(opt_txn_num, type, payload, std::forward<U...>(bufs...));
    }
}

MONAD_NAMESPACE_END
