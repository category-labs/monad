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

// A shard's four streams hold these records:
//
//   eth_header := rlp(header)
//   account    := encode_account_db(address, account) ...
//   storage    := group* (V2), or [account_offset: uint64][entry] ... (V0, V1)
//   code       := [size: uint64][code] ...
//
//   group      := [account_offset: uint64][payload_len: uint32][entry ...]
//   entry      := encode_storage_db(slot_key, slot_value)
//
// account_offset locates the owning account in the shard's account stream,
// counting from its first record, not from the stream header. A group holds
// every non-zero slot of one source storage leaf in ascending key order, no
// other group repeats any of them, and payload_len is never zero. When
// group_key_shift is at least the target's page-key shift, each target page
// lies within one group, so the loader can emit it as the group ends. An
// ungrouped record reads as a group of one slot.
//
// Every non-empty stream opens with monad_snapshot_stream_header except under
// V0. A reader detects the header by its magic, so it still loads V0, and a
// binary predating the header can restore only V0.
//
// Scalars are native-endian, which the format takes to be little-endian.
inline constexpr uint32_t MONAD_SNAPSHOT_STREAM_MAGIC = 0x5347534d; // "MSGS"
inline constexpr uint8_t MONAD_SNAPSHOT_STREAM_VERSION = 2;
inline constexpr uint8_t MONAD_SNAPSHOT_STREAM_VERSION_UNGROUPED = 1;
inline constexpr uint8_t MONAD_SNAPSHOT_STREAM_GUARD = 0xff;
inline constexpr size_t MONAD_SNAPSHOT_STORAGE_GROUP_HEADER_SIZE =
    sizeof(uint64_t) + sizeof(uint32_t);

struct monad_snapshot_stream_header
{
    uint32_t magic;
    uint8_t version;
    // The monad_snapshot_type this stream holds, so a stream file of the wrong
    // kind is rejected rather than misparsed. Nothing here identifies the
    // shard, so files swapped between shards still load.
    uint8_t kind;
    // Zero except on a storage stream, where it is the number of low slot-key
    // bits a group ignores: a group holds every non-zero slot sharing the
    // rest. Never zero in version 2, as one-slot groups would cost more than
    // version 1 records; reserved in version 1, whose readers ignore it.
    uint8_t group_key_shift;
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

// Snapshot bytes the loader buffers before an intermediate upsert, which bounds
// its memory except as monad_db_snapshot_loader_set_flush_bytes notes. Each
// flush costs an extra merklizing upsert, so this sits well above a typical
// shard; every shard is also flushed when its load ends.
inline constexpr uint64_t MONAD_SNAPSHOT_DEFAULT_FLUSH_BYTES = 10ull << 30;

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

// The stream layout a dump writes. It decides how old a binary can restore the
// dump, not what this one reads: V0 predates the stream header, V1 predates
// grouping. Above V0 the enumerator is written as the header's version. V2
// asked of a slot-encoded db is written as V1, as that db has nothing to group.
enum monad_snapshot_format
{
    MONAD_SNAPSHOT_FORMAT_V0 = 0,
    MONAD_SNAPSHOT_FORMAT_V1 = 1,
    MONAD_SNAPSHOT_FORMAT_V2 = 2
};

bool monad_db_dump_snapshot(
    char const *dbname_path, unsigned sq_thread_cpu, uint64_t block,
    uint64_t (*write)(
        uint64_t shard, enum monad_snapshot_type, unsigned char const *bytes,
        size_t len, void *user),
    void *user, unsigned dump_concurrency_limit, uint64_t total_shards,
    uint64_t shard_number, bool dump_from_secondary,
    enum monad_snapshot_format format);

struct monad_db_snapshot_loader *monad_db_snapshot_loader_create(
    uint64_t block, char const *dbname_path, unsigned sq_thread_cpu,
    bool load_to_secondary);

// Override MONAD_SNAPSHOT_DEFAULT_FLUSH_BYTES. Storage ignores it when a
// page-encoded target reads it ungrouped, as from any V0 or V1 dump, since a
// page there is complete only once the whole shard has been read.
void monad_db_snapshot_loader_set_flush_bytes(
    struct monad_db_snapshot_loader *loader, uint64_t bytes);

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

// A format is written verbatim as the header's version field, so the newest
// format and the newest stream version move together.
static_assert(
    MONAD_SNAPSHOT_FORMAT_V1 == MONAD_SNAPSHOT_STREAM_VERSION_UNGROUPED);
static_assert(MONAD_SNAPSHOT_FORMAT_V2 == MONAD_SNAPSHOT_STREAM_VERSION);
#endif
