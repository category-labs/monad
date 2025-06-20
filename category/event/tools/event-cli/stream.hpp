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

#include "command.hpp"

#include <chrono>
#include <cstddef>
#include <format>
#include <print>
#include <span>
#include <string>
#include <system_error>
#include <unordered_map>
#include <vector>

#include <errno.h>
#include <stdio.h>

#include <category/core/event/event_def.h>

extern char const *__progname;

struct EventIterator;
struct StreamObserver;

enum class EventIteratorResult : unsigned;

struct StreamObserver
{
    void *state;
    Command *command;
    std::chrono::system_clock start_time;

    EventSourceSpec const &get_event_source() const
    {
        return command->event_sources.front();
    }

    template <typename T>
    T *get_state()
    {
        return static_cast<T *>(state);
    }

    template <typename T>
    T const *get_state() const
    {
        return static_cast<T const *>(state);
    }
};

struct StreamEvent
{
    EventIteratorResult iter_result;
    monad_event_descriptor event;
    std::byte const *payload;
    size_t poll_count;
    size_t event_count;
    size_t gap_count;
};

enum class StreamUpdateResult
{
    Ok,
    Abort,
};

struct StreamObserverOps
{
    std::string (*init)(StreamObserver *);
    std::string (*iter_init)(StreamObserver *, EventIterator *);
    StreamUpdateResult (*update)(
        StreamObserver *, EventIterator *, StreamEvent *);
    void (*finish)(StreamObserver *, StreamUpdateResult);
};

void stream_thread_main(std::span<StreamObserver *const>);

std::string rewind_to_block_boundary(StreamObserver const *, EventIterator *);

extern StreamObserverOps const blockstat_ops;
extern StreamObserverOps const digest_ops;
extern StreamObserverOps const dump_ops;
extern StreamObserverOps const execstat_ops;
extern StreamObserverOps const record_ops;
extern StreamObserverOps const recordexec_ops;
extern StreamObserverOps const snapshot_ops;

constexpr StreamObserverOps const *get_stream_observer_ops(Command::Type type)
{
    using enum Command::Type;
    switch (type) {
    case BlockStat:
        return &blockstat_ops;
    case Digest:
        return &digest_ops;
    case Dump:
        return &dump_ops;
    case ExecStat:
        return &execstat_ops;
    case Record:
        return &record_ops;
    case RecordExec:
        return &recordexec_ops;
    case Snapshot:
        return &snapshot_ops;
    default:
        return nullptr;
    }
}

template <typename... Args>
void stream_warnc_f(
    StreamObserver *so, std::error_condition const &ec,
    std::format_string<Args...> fmt, Args &&...args)
{
    std::print(
        stderr,
        "{}: command={} source={}: ",
        __progname,
        describe(so->command->type),
        so->command->event_sources.front().describe());
    std::print(stderr, fmt, std::forward<Args>(args)...);
    if (ec) {
        std::println(stderr, ": {} [{}]", ec.message(), ec.value());
    }
    else {
        std::println(stderr);
    }
}

template <typename... Args>
void stream_warn_f(
    StreamObserver *so, std::format_string<Args...> fmt, Args &&...args)
{
    stream_warnc_f(
        so, static_cast<std::errc>(errno), fmt, std::forward<Args>(args)...);
}

template <typename... Args>
void stream_warnx_f(
    StreamObserver *so, std::format_string<Args...> fmt, Args &&...args)
{
    stream_warnc_f(so, {}, fmt, std::forward<Args>(args)...);
}

#define VBUF_CHECK_INIT(X)                                                     \
    if ((X) != 0) [[unlikely]] {                                               \
        return std::format(                                                    \
            "{}: vbuf library error -- {}",                                    \
            __progname,                                                        \
            monad_vbuf_writer_get_last_error());                               \
    }

#define EVCAP_CHECK_INIT(X)                                                    \
    if ((X) != 0) [[unlikely]] {                                               \
        return std::format(                                                    \
            "{}: evcap library error -- {}",                                   \
            __progname,                                                        \
            monad_evcap_writer_get_last_error());                              \
    }

#define BCAP_CHECK_INIT(X)                                                     \
    if ((X) != 0) [[unlikely]] {                                               \
        return std::format(                                                    \
            "{}: bcap library error -- {}",                                    \
            __progname,                                                        \
            monad_bcap_get_last_error());                                      \
    }

#define VBUF_CHECK_UPDATE(X)                                                   \
    if ((X) != 0) [[unlikely]] {                                               \
        stream_warnx_f(                                                        \
            so,                                                                \
            "vbuf library error -- {}",                                        \
            monad_vbuf_writer_get_last_error());                               \
        return StreamUpdateResult::Abort;                                      \
    }

#define BCAP_CHECK_UPDATE(X)                                                   \
    if ((X) != 0) [[unlikely]] {                                               \
        stream_warnx_f(                                                        \
            so, "bcap library error -- {}", monad_bcap_get_last_error());      \
        return StreamUpdateResult::Abort;                                      \
    }
