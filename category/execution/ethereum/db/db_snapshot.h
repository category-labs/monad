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
//   storage    := group*
//   code       := [size: uint64][code] ...
//
//   group      := [account_offset: uint64][payload_len: uint32][payload]
//
// Each group is prefixed by the offset of the owning account within the shard's
// account stream, and holds the encode_storage_db(slot_key, slot_value) entries
// of one storage leaf of the source db, in ascending slot-key order.
// payload_len is never zero. Account offsets count from the first account
// record, not from the stream header, so they do not depend on whether the
// header is present.
//
// A group is closed: it holds every non-zero slot of its source leaf, and no
// later group in the stream repeats any of them. When group_key_shift is also
// at least as coarse as the target's page key, that is what lets the loader
// emit a finished page as its group ends instead of buffering a whole shard.
//
// Two older storage layouts must also be read. A version 1 header, and no
// header at all, both denote ungrouped storage records:
//
//   storage := [account_offset: uint64][one encode_storage_db entry] ...
//
// which the loader reads as groups of a single slot. No header at all is how a
// snapshot written before headers existed is recognised; nothing outside the
// storage stream differs between version 1 and version 2.
//
// Scalars are native-endian, which the format takes to be little-endian.
inline constexpr uint32_t MONAD_SNAPSHOT_STREAM_MAGIC = 0x5347534d; // "MSGS"
inline constexpr uint8_t MONAD_SNAPSHOT_STREAM_VERSION = 2;
// Version 1 framed every stream the same way but held one slot entry per
// storage record, and left the group_key_shift byte reserved.
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
    // Meaning depends on kind; zero for every kind but MONAD_SNAPSHOT_STORAGE,
    // where it is the number of low slot-key bits that do not participate in
    // grouping: a group holds every non-zero slot sharing the remaining high
    // bits. Zero there too means one slot per group, which groups nothing.
    // Reserved in version 1, whose readers were told to accept any value, so it
    // carries no meaning for a version 1 stream.
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

// Snapshot bytes the loader buffers before an intermediate upsert. This bounds
// its peak memory, except for storage the loader cannot close page by page (see
// monad_db_snapshot_loader_set_flush_bytes). Each flush costs one extra
// incremental merklizing upsert, so it is set well above a typical shard and
// only bites on outsized ones. A shard is flushed when its load ends whatever
// the threshold, which is what keeps its buffered storage from outliving it.
inline constexpr uint64_t MONAD_SNAPSHOT_DEFAULT_FLUSH_BYTES = 1ull << 30;

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

// Override MONAD_SNAPSHOT_DEFAULT_FLUSH_BYTES. Storage honours it only when the
// loader can close pages as it reads, that is when the target is slot-encoded
// or the stream's group_key_shift covers a whole target page. Otherwise — a
// page-encoded target reading a stream whose groups hold one slot each, which
// is every stream dumped from a slot-encoded db and every stream with no header
// at all — a shard's storage has to be assembled in full before any of it can
// be written.
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
#endif
