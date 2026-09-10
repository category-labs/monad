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

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_sync_type : uint8_t
{
    SYNC_TYPE_REQUEST = 0,
    SYNC_TYPE_TARGET = 1,
    SYNC_TYPE_DONE = 2,
    SYNC_TYPE_UPSERT_CODE = 3,
    SYNC_TYPE_UPSERT_ACCOUNT = 4,
    SYNC_TYPE_UPSERT_STORAGE = 5,
    SYNC_TYPE_UPSERT_ACCOUNT_DELETE = 6,
    SYNC_TYPE_UPSERT_STORAGE_DELETE = 7,
    SYNC_TYPE_UPSERT_HEADER = 8,
    // One page-encoded storage leaf: the 20-byte address followed by the page
    // leaf verbatim, exactly as the server holds it, page key included.
    SYNC_TYPE_UPSERT_STORAGE_PAGE = 9,
};

static_assert(sizeof(enum monad_sync_type) == 1);
static_assert(alignof(enum monad_sync_type) == 1);

struct monad_sync_request
{
    uint64_t prefix;
    uint8_t prefix_bytes;
    uint64_t target;
    uint64_t from;
    uint64_t until;
    uint64_t old_target;
    // protocol version the requester speaks; the server serves the newest wire
    // this permits. Authoritative only on requests arriving at a server, where
    // bft sets it from the requesting peer's negotiated version. On a request
    // the local client generates, bft substitutes its own version before the
    // request reaches the network, so the value set here reaches only an
    // in-process server.
    uint32_t version;
};

static_assert(sizeof(struct monad_sync_request) == 56);
static_assert(alignof(struct monad_sync_request) == 8);

struct monad_sync_done
{
    bool success;
    uint64_t prefix;
    uint64_t n;
};

static_assert(sizeof(struct monad_sync_done) == 24);
static_assert(alignof(struct monad_sync_done) == 8);

#ifdef __cplusplus
}
#endif
