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

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus

inline constexpr unsigned MONAD_SNAPSHOT_SHARD_NIBBLES = 2;
inline constexpr unsigned MONAD_SNAPSHOT_SHARDS =
    1 << (MONAD_SNAPSHOT_SHARD_NIBBLES * 4);
static_assert(MONAD_SNAPSHOT_SHARDS == 256);

extern "C"
{
#endif

struct monad_db_snapshot_loader;

enum monad_snapshot_type
{
    MONAD_SNAPSHOT_ETH_HEADER = 0,
    MONAD_SNAPSHOT_ACCOUNT,
    MONAD_SNAPSHOT_STORAGE,
    MONAD_SNAPSHOT_CODE
};

bool monad_db_dump_snapshot(
    char const *const *dbname_paths, size_t len, unsigned sq_thread_cpu,
    uint64_t block,
    uint64_t (*write)(
        uint64_t shard, enum monad_snapshot_type, unsigned char const *bytes,
        size_t len, void *user),
    void *user, unsigned dump_concurrency_limit, uint64_t total_shards,
    uint64_t shard_number);

struct monad_db_snapshot_loader *monad_db_snapshot_loader_create(
    uint64_t block, char const *const *dbname_paths, size_t len,
    unsigned sq_thread_cpu);

void monad_db_snapshot_loader_load(
    struct monad_db_snapshot_loader *loader, uint64_t shard,
    unsigned char const *eth_header, size_t, unsigned char const *account,
    size_t, unsigned char const *storage, size_t, unsigned char const *code,
    size_t);

void monad_db_snapshot_loader_destroy(struct monad_db_snapshot_loader *);

#ifdef __cplusplus
}
#endif
