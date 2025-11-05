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

#include <category/core/config.hpp>
#include <category/statesync/statesync_messages.h>

#ifdef __cplusplus
extern "C"
{
#endif

extern unsigned const MONAD_SQPOLL_DISABLED;

struct monad_statesync_client;
struct monad_statesync_client_context;

struct monad_statesync_client_context *monad_statesync_client_context_create(
    char const *const *dbname_paths, size_t len, unsigned sq_thread_cpu,
    struct monad_statesync_client *,
    void (*statesync_send_request)(
        struct monad_statesync_client *,
        struct monad_sync_request)) MONAD_NOEXCEPT;

uint8_t monad_statesync_client_prefix_bytes() MONAD_NOEXCEPT;

size_t monad_statesync_client_prefixes() MONAD_NOEXCEPT;

bool monad_statesync_client_has_reached_target(
    struct monad_statesync_client_context const *) MONAD_NOEXCEPT;

void monad_statesync_client_handle_new_peer(
    struct monad_statesync_client_context *, uint64_t prefix,
    uint32_t version) MONAD_NOEXCEPT;

void monad_statesync_client_handle_target(
    struct monad_statesync_client_context *, unsigned char const *,
    uint64_t) MONAD_NOEXCEPT;

bool monad_statesync_client_handle_upsert(
    struct monad_statesync_client_context *, uint64_t prefix,
    enum monad_sync_type, unsigned char const *, uint64_t) MONAD_NOEXCEPT;

void monad_statesync_client_handle_done(
    struct monad_statesync_client_context *,
    struct monad_sync_done) MONAD_NOEXCEPT;

bool monad_statesync_client_finalize(struct monad_statesync_client_context *)
    MONAD_NOEXCEPT;

void monad_statesync_client_context_destroy(
    struct monad_statesync_client_context *) MONAD_NOEXCEPT;

#ifdef __cplusplus
}
#endif
