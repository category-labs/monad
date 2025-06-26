#pragma once

#include <monad/config.h>

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct monad_c_triedb monad_c_triedb;

BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_open(char const *dbpaths[], monad_c_triedb **);
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_close(monad_c_triedb *);

typedef uint8_t const *monad_c_triedb_bytes;
// returns -1 if key not found
// if >= 0, returns length of value
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_c_triedb_read(
    monad_c_triedb *, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    monad_c_triedb_bytes *value, uint64_t block_id);
// calls (*completed) when read is
// complete. Call triedb_finalize when
// done with the value.
extern void monad_c_triedb_async_read(
    monad_c_triedb *, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    uint64_t block_id,
    void (*completed)(monad_c_result value, size_t length, void *user),
    void *user);

// traverse the trie
enum triedb_async_traverse_callback
{
    triedb_async_traverse_callback_value,
    triedb_async_traverse_callback_finished_normally,
    triedb_async_traverse_callback_finished_early
};
// purely here to make Rust bindgen emit the above enum
extern enum triedb_async_traverse_callback
monad_c_triedb_make_rust_bindgen_emit_this_enum();

typedef void (*monad_c_triedb_callback_func)(
    monad_c_result kind /* value is enum triedb_async_traverse_callback */,
    void *context, monad_c_triedb_bytes path, size_t path_len,
    monad_c_triedb_bytes value, size_t value_len);
extern bool monad_c_triedb_traverse(
    monad_c_triedb *, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    uint64_t block_id, void *context, monad_c_triedb_callback_func callback);
extern void monad_c_triedb_async_traverse(
    monad_c_triedb *, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    uint64_t block_id, void *context, monad_c_triedb_callback_func callback);
extern void monad_c_triedb_async_ranged_get(
    monad_c_triedb *, monad_c_triedb_bytes prefix_key,
    uint8_t prefix_len_nibbles, monad_c_triedb_bytes min_key,
    uint8_t min_len_nibbles, monad_c_triedb_bytes max_key,
    uint8_t max_len_nibbles, uint64_t block_id, void *context,
    monad_c_triedb_callback_func callback);
// pumps async reads, processing no
// more than count maximum, returning
// how many were processed.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_poll(monad_c_triedb *, bool blocking, size_t count);
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_finalize(monad_c_triedb_bytes value);

// returns error if doesn't exist
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_latest_voted_block(monad_c_triedb *);
// returns error if doesn't exist
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_latest_voted_round(monad_c_triedb *);
// returns error if doesn't exist
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_latest_finalized_block(monad_c_triedb *);
// returns error if doesn't exist
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_latest_verified_block(monad_c_triedb *);

// returns error if doesn't exist
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_c_triedb_earliest_finalized_block(monad_c_triedb *);

#ifdef __cplusplus
}
#endif
