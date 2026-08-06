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

#include <category/execution/ethereum/db/db_snapshot.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_db_snapshot_filesystem_write_user_context;

struct monad_db_snapshot_filesystem_write_user_context *
monad_db_snapshot_filesystem_write_user_context_create(
    char const *root, uint64_t block);

void monad_db_snapshot_filesystem_write_user_context_destroy(
    struct monad_db_snapshot_filesystem_write_user_context *);

uint64_t monad_db_snapshot_write_filesystem(
    uint64_t shard, monad_snapshot_type, unsigned char const *bytes, size_t len,
    void *user);

/* load_concurrency is the number of threads that decode and prepare shards
   ahead of the upsert (0 = auto, 1 = serial). See
   monad_db_snapshot_loader_create for upsert_concurrency and
   partition_min_updates. */
void monad_db_snapshot_load_filesystem(
    char const *const *dbname_paths, size_t len, unsigned sq_thread_cpu,
    char const *snapshot_dir, uint64_t block, bool load_to_secondary,
    unsigned load_concurrency, unsigned upsert_concurrency,
    uint32_t partition_min_updates);

#ifdef __cplusplus
}
#endif
