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

typedef struct triedb triedb;

int triedb_open(char const *dbdirpath, triedb **, uint64_t node_lru_max_mem);
int triedb_close(triedb *);

// returns -1 if key not found
// if >= 0, returns length of value
int triedb_read(
    triedb *, uint8_t const *key, uint8_t key_len_nibbles,
    uint8_t const **value, uint64_t block_id);
// calls (*completed) when read is
// complete. length is -1 if key not
// found. If >=0, returns length of
// value. Call triedb_finalize when
// done with the value.
void triedb_async_read(
    triedb *, uint8_t const *key, uint8_t key_len_nibbles, uint64_t block_id,
    void (*completed)(uint8_t const *value, int length, void *user),
    void *user);

// traverse the trie.
enum triedb_async_traverse_callback
{
    triedb_async_traverse_callback_value,
    triedb_async_traverse_callback_finished_normally,
    triedb_async_traverse_callback_finished_early
};

typedef void (*callback_func)(
    enum triedb_async_traverse_callback kind, void *context,
    uint8_t const *path, size_t path_len, uint8_t const *value,
    size_t value_len);
bool triedb_traverse(
    triedb *, uint8_t const *key, uint8_t key_len_nibbles, uint64_t block_id,
    void *context, callback_func callback);
void triedb_async_traverse(
    triedb *, uint8_t const *key, uint8_t key_len_nibbles, uint64_t block_id,
    void *context, callback_func callback);
void triedb_async_ranged_get(
    triedb *, uint8_t const *prefix_key, uint8_t prefix_len_nibbles,
    uint8_t const *min_key, uint8_t min_len_nibbles, uint8_t const *max_key,
    uint8_t max_len_nibbles, uint64_t block_id, void *context,
    callback_func callback);
// pumps async reads, processing no
// more than count maximum, returning
// how many were processed.
size_t triedb_poll(triedb *, bool blocking, size_t count);
int triedb_finalize(uint8_t const *value);

// returns MAX if doesn't exist
uint64_t triedb_latest_proposed_block(triedb *);
// returns all-zeros if doesn't exist
monad_c_bytes32 triedb_latest_proposed_block_id(triedb *);
// returns MAX if doesn't exist
uint64_t triedb_latest_voted_block(triedb *);
// returns all-zeros if doesn't exist
monad_c_bytes32 triedb_latest_voted_block_id(triedb *);
// returns MAX if doesn't exist
uint64_t triedb_latest_finalized_block(triedb *);
// returns MAX if doesn't exist
uint64_t triedb_latest_verified_block(triedb *);

// returns MAX if doesn't exist
uint64_t triedb_earliest_finalized_block(triedb *);

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
triedb_read_valset(triedb *, size_t block_num, uint64_t requested_epoch);

#ifdef __cplusplus
}
#endif
