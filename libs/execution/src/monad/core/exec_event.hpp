#pragma once

/**
 * @file
 *
 * This file defines the execution event recorder. It is up to the frontend
 * process to configure the recorder in this library, otherwise recording will
 * remain disabled.
 */

#include <monad/config.hpp>
#include <monad/event/event_recorder.h>

#include <span>

struct iovec;

MONAD_NAMESPACE_BEGIN

extern monad_event_recorder *g_monad_execution_recorder;

template <typename T>
void record_exec_event(monad_event_type type, T const &t)
{
    monad_event_record(g_monad_execution_recorder, type, &t, sizeof t);
}

inline void
record_exec_event_iov(monad_event_type type, std::span<iovec const> iov)
{
    monad_event_recordv(
        g_monad_execution_recorder, type, iov.data(), iov.size());
}

MONAD_NAMESPACE_END
