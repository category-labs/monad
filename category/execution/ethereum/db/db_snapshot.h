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

    #include <bit>

inline constexpr unsigned MONAD_SNAPSHOT_SHARD_NIBBLES = 2;
inline constexpr unsigned MONAD_SNAPSHOT_SHARDS =
    1 << (MONAD_SNAPSHOT_SHARD_NIBBLES * 4);
static_assert(MONAD_SNAPSHOT_SHARDS == 256);

// Number of files written per shard, one per monad_snapshot_type (eth_header,
// account, storage, code). The filesystem dumper holds this many file
// descriptors open per active shard for the whole dump, so a run needs roughly
// (active shards) * MONAD_SNAPSHOT_FILES_PER_SHARD descriptors at its peak.
inline constexpr unsigned MONAD_SNAPSHOT_FILES_PER_SHARD = 4;

// Every non-empty stream of a shard opens with monad_snapshot_stream_header,
// followed by that stream's records:
//
//   eth_header := rlp(header)
//   account    := encode_account_db(address, account) ...
//   storage    := [account_offset: uint64][encode_storage_db(key, value)] ...
//   code       := [size: uint64][code] ...
//
// A storage record is prefixed by the offset of the owning account within the
// shard's account stream, which is how the loader relinks it whatever order the
// records arrive in. Those offsets count from the first account record rather
// than from the stream header, so they do not depend on whether the header is
// present.
//
// A dump always writes the header, but a reader must also accept a stream that
// lacks one and parse its records from byte 0: that is how a snapshot written
// before the header existed is recognised.
//
// Scalars are native-endian, which the format takes to be little-endian.
inline constexpr uint32_t MONAD_SNAPSHOT_STREAM_MAGIC = 0x5347534d; // "MSGS"
inline constexpr uint8_t MONAD_SNAPSHOT_STREAM_VERSION = 1;
inline constexpr uint8_t MONAD_SNAPSHOT_STREAM_GUARD = 0xff;

struct monad_snapshot_stream_header
{
    uint32_t magic;
    uint8_t version;
    // The monad_snapshot_type this stream holds, so a stream file of the wrong
    // kind is rejected rather than misparsed. Nothing here identifies the
    // shard, so files swapped between shards still load.
    uint8_t kind;
    // Zero. Readers ignore it, so a later revision may give it a meaning
    // without a version bump only if an unaware reader can correctly skip it.
    uint8_t reserved;
    // MONAD_SNAPSHOT_STREAM_GUARD. The magic's first byte on disk is below
    // 0xc0, so a header can never be mistaken for the RLP list that opens an
    // eth_header or account stream; the guard is the most significant byte when
    // the eight are read as the leading uint64 of a storage or code stream,
    // putting them above 2^56 where an account offset or a code length never
    // reaches. A binary predating the header therefore aborts on the bogus
    // value rather than misreading.
    uint8_t guard;
};

static_assert(sizeof(struct monad_snapshot_stream_header) == 8);
// Both properties the guard comment relies on are positional, and hold only
// where the magic's low byte and the guard are respectively the first and last
// of the eight bytes on disk.
static_assert(std::endian::native == std::endian::little);
static_assert((MONAD_SNAPSHOT_STREAM_MAGIC & 0xff) < 0xc0);

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
    uint64_t shard_number, bool dump_from_secondary);

struct monad_db_snapshot_loader *monad_db_snapshot_loader_create(
    uint64_t block, char const *const *dbname_paths, size_t len,
    unsigned sq_thread_cpu, bool load_to_secondary);

void monad_db_snapshot_loader_load(
    struct monad_db_snapshot_loader *loader, uint64_t shard,
    unsigned char const *eth_header, size_t, unsigned char const *account,
    size_t, unsigned char const *storage, size_t, unsigned char const *code,
    size_t);

void monad_db_snapshot_loader_destroy(struct monad_db_snapshot_loader *);

#ifdef __cplusplus
}

// The dumper indexes per-kind state by monad_snapshot_type, so a new kind needs
// a wider array rather than a runtime out_of_range mid-dump.
static_assert(MONAD_SNAPSHOT_CODE + 1 == MONAD_SNAPSHOT_FILES_PER_SHARD);
#endif
