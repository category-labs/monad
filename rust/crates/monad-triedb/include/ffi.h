// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/execution/ethereum/core/base_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct TriedbRoInner TriedbRoInner;

int triedb_open(
    char const *dbdirpath, TriedbRoInner **, uint64_t node_lru_max_mem);
int triedb_close(TriedbRoInner *);

// returns -1 if key not found
// if >= 0, returns length of value
int triedb_read(
    TriedbRoInner *, uint8_t const *key, uint8_t key_len_nibbles,
    uint8_t const **value, uint64_t block_id);

// true if the primary timeline is page-encoded (Monad state machine), in which
// case storage is keyed by keccak(page_key) (page_key = slot >> 7) and the leaf
// is an encoded page; otherwise storage is slot-encoded.
bool triedb_is_page_encoded(TriedbRoInner *);

// Compute the storage page key for a 32-byte slot key on a page-encoded db:
// page_key = slot >> 7. Writes the 32-byte big-endian page key (the key the
// storage trie is looked up by) to out_page_key.
void triedb_compute_page_key(uint8_t const *slot_key, uint8_t *out_page_key);

// Compute the slot's offset within its page for a 32-byte slot key: the low 7
// bits of the slot key. This is the `offset` argument to
// triedb_decode_storage_page_slot.
uint8_t triedb_compute_slot_offset(uint8_t const *slot_key);

// Decode a page-encoded storage leaf (as returned by triedb_read for a
// page-encoded db, looked up with the page key) and write the 32-byte value of
// the slot at `offset` (the low 7 bits of the original slot key) to out_value.
// Returns false on decode error.
bool triedb_decode_storage_page_slot(
    uint8_t const *leaf, size_t leaf_len, uint8_t offset, uint8_t *out_value);

typedef void (*triedb_async_read_callback_fn)(
    uint8_t const *value, int length, void *user);
// calls (*completed) when read is
// complete. length is -1 if key not
// found. If >=0, returns length of
// value. Call triedb_finalize when
// done with the value.
void triedb_async_read(
    TriedbRoInner *, uint8_t const *key, uint8_t key_len_nibbles,
    uint64_t block_id, triedb_async_read_callback_fn callback, void *user);

// traverse the trie.
enum triedb_async_traverse_callback
{
    triedb_async_traverse_callback_value,
    triedb_async_traverse_callback_finished_normally,
    triedb_async_traverse_callback_finished_early
};

typedef void (*triedb_async_traverse_callback_fn)(
    enum triedb_async_traverse_callback kind, void *context,
    uint8_t const *path, size_t path_len, uint8_t const *value,
    size_t value_len);
bool triedb_traverse(
    TriedbRoInner *, uint8_t const *key, uint8_t key_len_nibbles,
    uint64_t block_id, void *context,
    triedb_async_traverse_callback_fn callback);
void triedb_async_traverse(
    TriedbRoInner *, uint8_t const *key, uint8_t key_len_nibbles,
    uint64_t block_id, void *context,
    triedb_async_traverse_callback_fn callback);
void triedb_async_ranged_get(
    TriedbRoInner *, uint8_t const *prefix_key, uint8_t prefix_len_nibbles,
    uint8_t const *min_key, uint8_t min_len_nibbles, uint8_t const *max_key,
    uint8_t max_len_nibbles, uint64_t block_id, void *context,
    triedb_async_traverse_callback_fn callback);
// pumps async reads, processing no
// more than count maximum, returning
// how many were processed.
size_t triedb_poll(TriedbRoInner *, bool blocking, size_t count);
int triedb_finalize(uint8_t const *value);

// returns MAX if doesn't exist
uint64_t triedb_latest_proposed_version(TriedbRoInner *);
// returns all-zeros if doesn't exist
monad_c_bytes32 triedb_latest_proposed_block_id(TriedbRoInner *);
// returns MAX if doesn't exist
uint64_t triedb_latest_voted_version(TriedbRoInner *);
// returns all-zeros if doesn't exist
monad_c_bytes32 triedb_latest_voted_block_id(TriedbRoInner *);
// returns MAX if doesn't exist
uint64_t triedb_latest_finalized_version(TriedbRoInner *);
// returns MAX if doesn't exist
uint64_t triedb_latest_verified_version(TriedbRoInner *);

// returns MAX if doesn't exist
uint64_t triedb_earliest_version(TriedbRoInner *);
// returns MAX if doesn't exist
uint64_t triedb_latest_version(TriedbRoInner *);

#pragma pack(push, 1)

typedef struct validator_data
{
    uint8_t secp_pubkey[33];
    uint8_t bls_pubkey[48];
    // big endian u256
    uint8_t stake[32];
} validator_data;

typedef struct validator_set
{
    struct validator_data *validators;
    uint64_t length;
} validator_set;

#pragma pack(pop)

void triedb_free_valset(validator_set *);

validator_set *
triedb_read_valset(TriedbRoInner *, size_t block_num, uint64_t requested_epoch);

// ── KV-DB prototype (RPC read side) ─────────────────────────────────────────
// A separate read-only opener over the flat-page KV store (the read authority
// for state + per-block data), with hazard-pointer block protection so the RPC
// process reads are safe against exec's concurrent reclamation. Independent of
// TriedbRoInner (different backend); exec must be running (see kv_open).
typedef struct KvReaderHandle KvReaderHandle;

// Open read-only. `kvhdr_path` is the .kvhdr sidecar (gives the device layout);
// the block device is taken from $KVDB_DEVICE (default /dev/triedb). Returns 0 on
// success (writes *out), <0 on failure (exec not up, bad header, etc.).
int kv_open(char const *kvhdr_path, KvReaderHandle **out);
int kv_close(KvReaderHandle *);

// Pin a block for the lifetime of a request: walk the block map under a transient
// hazard, publish the block root on a request-long hazard, drop the transient.
// Returns an opaque handle (>= 0) that protects the block root against
// reclamation, or -1 if `block` is not retained (pruned / never existed). Pass
// the handle to the KV state/data reads (added next), then release it with
// kv_end_block_protection.
//
// `id` is the 32-byte proposal id for an undecided block. Pass NULL for the
// finalized block at that height, whose entry finalize made unique; an
// undecided height can carry several proposals, so there it must be given.
int64_t
kv_try_protect_block(KvReaderHandle *, uint64_t block, uint8_t const *id);
void kv_end_block_protection(KvReaderHandle *, int64_t handle);

// Per-block blob categories (the block root's children). Whole-blob categories
// are read with kv_read_block_blob; the per-tx ones (receipts, transactions,
// call frames) index a single tx with kv_read_tx_blob.
enum kv_blob_category
{
    kv_blob_receipts = 0,
    kv_blob_transactions = 1,
    kv_blob_header = 2,
    kv_blob_call_frames = 3,
    kv_blob_ommers = 4,
    kv_blob_withdrawals = 5,
    kv_blob_tx_hashes = 6
};

#pragma pack(push, 1)

// An account as KV stores it, in an explicit FFI layout (no RLP, no dependence
// on the C++ uint256 representation). `balance` is 32-byte big-endian.
// `code_hash` is the raw hash and equals keccak256("") -- alloy's
// KECCAK256_EMPTY -- when the account has no code, which is exactly the case
// where the triedb RLP path yields code_hash = None.
typedef struct kv_account
{
    uint8_t balance[32];
    uint8_t code_hash[32];
    uint64_t nonce;
} kv_account;

// All four block-tag cursors at once, with the ids of the proposed and voted
// heads. Block numbers are UINT64_MAX when the tag has never been stamped.
typedef struct kv_tags
{
    uint64_t finalized;
    uint64_t earliest;
    uint64_t proposed;
    uint8_t proposed_id[32];
    uint64_t voted;
    uint8_t voted_id[32];
} kv_tags;

#pragma pack(pop)

// State reads under a protected handle. Return true if the account exists.
bool kv_read_account(
    KvReaderHandle *, int64_t handle, uint8_t const *addr, kv_account *out);
// Writes the 32-byte slot value, all-zero when absent (KV stores no zero slots).
void kv_read_storage(
    KvReaderHandle *, int64_t handle, uint8_t const *addr, uint8_t const *key,
    uint8_t *out_value);

// Code by hash. Takes no handle: the code tree is grow-only and never reclaimed.
bool kv_read_code(
    KvReaderHandle *, uint8_t const *code_hash, uint8_t const **value,
    uint64_t *len);

// Per-block data under a protected handle. False if the category (or that tx) is
// absent for the block.
bool kv_read_block_blob(
    KvReaderHandle *, int64_t handle, uint32_t category, uint8_t const **value,
    uint64_t *len);
bool kv_read_tx_blob(
    KvReaderHandle *, int64_t handle, uint32_t category, uint32_t tx_index,
    uint8_t const **value, uint64_t *len);

// Is a blob category present for this block at all? Use before kv_read_tx_blob
// on a per-tx category (a whole-blob read of a table category is not valid).
bool kv_blob_present(KvReaderHandle *, int64_t handle, uint32_t category);
// How many txs a per-tx table category covers; -1 if absent or not a table.
int64_t kv_table_count(KvReaderHandle *, int64_t handle, uint32_t category);

// Free a buffer from kv_read_code / kv_read_block_blob / kv_read_tx_blob.
// nullptr is a no-op.
void kv_free(uint8_t const *value);

// Global hash indexes: turn a user-supplied hash into a locator. Resolution-only
// and pre-pin, so no handle -- a transient hazard is taken internally.
bool kv_resolve_tx_hash(
    KvReaderHandle *, uint8_t const *hash, uint64_t *block,
    uint32_t *tx_index);
bool kv_resolve_block_hash(
    KvReaderHandle *, uint8_t const *hash, uint64_t *number);

// Block-tag cursors from KV's metadata. Proposed/voted are UINT64_MAX until
// consensus first stamps them.
uint64_t kv_finalized_block(KvReaderHandle *);
uint64_t kv_earliest_block(KvReaderHandle *);
uint64_t kv_proposed_block(KvReaderHandle *);
uint64_t kv_voted_block(KvReaderHandle *);

// All four at once, as one consistent snapshot -- which is what block-tag
// resolution needs, since it reads finalized, voted and proposed together.
// False if no stable (block, id) pair could be read; the caller should then
// keep whatever it had rather than act on a torn one.
bool kv_read_tags(KvReaderHandle *, kv_tags *out);

#ifdef __cplusplus
}
#endif
