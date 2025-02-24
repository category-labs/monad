#pragma once

/**
 * @file
 *
 * This file provides execution event recording functions for C++. These are
 * inline functions and templates that provide idiomatic C++ alternatives to
 * the C recording macros from event_recorder.h
 */

#include <monad/config.hpp>
#include <monad/event/event_recorder.h>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

template <typename T>
void record_event_expr(monad_event_type type, T const &t, uint8_t flags = 0)
{
    MONAD_EVENT_EXPR(type, flags, t);
}

inline void record_event_iov(
    monad_event_type type, std::span<iovec const> iov, uint8_t flags = 0)
{
    MONAD_EVENT_IOV(type, flags, iov.data(), iov.size());
}

MONAD_NAMESPACE_END
