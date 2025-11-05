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

struct monad_statesync_server;
struct monad_statesync_server_context;
struct monad_statesync_server_network;

struct monad_statesync_server *monad_statesync_server_create(
    struct monad_statesync_server_context *,
    struct monad_statesync_server_network *,
    ssize_t (*statesync_server_recv)(
        struct monad_statesync_server_network *, unsigned char *, size_t),
    void (*statesync_server_send_upsert)(
        struct monad_statesync_server_network *, enum monad_sync_type,
        unsigned char const *v1, uint64_t size1, unsigned char const *v2,
        uint64_t size2),
    void (*statesync_server_send_done)(
        struct monad_statesync_server_network *,
        struct monad_sync_done)) MONAD_NOEXCEPT;

void monad_statesync_server_run_once(struct monad_statesync_server *)
    MONAD_NOEXCEPT;

void monad_statesync_server_destroy(struct monad_statesync_server *)
    MONAD_NOEXCEPT;
