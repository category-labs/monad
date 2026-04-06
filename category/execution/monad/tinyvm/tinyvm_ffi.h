// Copyright (C) 2026 Category Labs, Inc.
//
// TinyVM generic FFI — single entry point for all backends.
// Rust owns verification + state logic; C++ provides State via callbacks.

#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// Callbacks from Rust into C++ EVM State.
typedef int (*tinyvm_store_get_fn)(
    void *ctx,
    uint8_t const *key, size_t key_len,
    uint8_t *value_buf, size_t value_buf_len,
    size_t *value_len);

typedef void (*tinyvm_store_set_fn)(
    void *ctx,
    uint8_t const *key, size_t key_len,
    uint8_t const *value, size_t value_len);

typedef struct tinyvm_apply_result
{
    unsigned __int128 escrow_refund;
    uint8_t token[32];       // token involved
    uint8_t owner[20];       // owner for unshield refund transfer
    uint8_t success;         // 1 = ok, 0 = revert
} tinyvm_apply_result;

// Returns gas cost for a TinyVM call, or 0 on decode failure.
uint64_t tinyvm_gas_cost(uint8_t const *input, size_t input_len);

// Generic TinyVM entry point.
// Decodes envelope, dispatches to backend, verifies proofs,
// reads/writes state via callbacks, returns escrow refund.
// Logs are serialized into logs_buf as:
//   [num_logs: u32 LE]
//   for each log:
//     [num_topics: u32 LE] [topic0..topicN: 32 bytes each]
//     [data_len: u32 LE] [data: data_len bytes]
int tinyvm_apply(
    uint8_t const *sender, size_t sender_len,
    // TODO: pass tx_value as raw 32 bytes (u256) and let the backend handle truncation
    uint64_t tx_value_lo, uint64_t tx_value_hi,
    uint8_t const *input, size_t input_len,
    void *store_ctx,
    tinyvm_store_get_fn store_get,
    tinyvm_store_set_fn store_set,
    tinyvm_apply_result *result,
    uint8_t *logs_buf, size_t logs_buf_len, size_t *logs_written,
    char *error_buf, size_t error_len);

#ifdef __cplusplus
}
#endif
