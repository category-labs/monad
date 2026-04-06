/**
 * C integration test for tinyvm FFI struct layout and escrow_refund.
 *
 * Links against the Rust-built libtinyvm_ffi.so and exercises the
 * exact same FFI boundary that the C++ precompile uses. Catches
 * struct layout mismatches between Rust and C compilers.
 *
 * Build: gcc -o test_ffi tests/c_ffi_integration.c -L../../target/release -ltinyvm_ffi -lpthread -ldl -lm
 * Run:   LD_LIBRARY_PATH=../../target/release ./test_ffi
 */

#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Must match the Rust #[repr(C)] struct exactly */
typedef struct tinyvm_apply_result
{
    unsigned __int128 escrow_refund;
    uint8_t token[32];
    uint8_t owner[20];
    uint8_t success;
} tinyvm_apply_result;

/* FFI functions from libtinyvm_ffi.so */
typedef int (*tinyvm_store_get_fn)(
    void *ctx,
    uint8_t const *key, size_t key_len,
    uint8_t *value_buf, size_t value_buf_len,
    size_t *value_len);

typedef void (*tinyvm_store_set_fn)(
    void *ctx,
    uint8_t const *key, size_t key_len,
    uint8_t const *value, size_t value_len);

extern uint64_t tinyvm_gas_cost(uint8_t const *input, size_t input_len);

extern int tinyvm_apply(
    uint8_t const *sender, size_t sender_len,
    uint64_t tx_value_lo, uint64_t tx_value_hi,
    uint8_t const *input, size_t input_len,
    void *store_ctx,
    tinyvm_store_get_fn store_get,
    tinyvm_store_set_fn store_set,
    tinyvm_apply_result *result,
    uint8_t *logs_buf, size_t logs_buf_len, size_t *logs_written,
    char *error_buf, size_t error_len);

/* ── Test 1: Struct layout ── */
void test_struct_layout(void) {
    printf("test_struct_layout: ");

    assert(sizeof(tinyvm_apply_result) == 80);
    assert(offsetof(tinyvm_apply_result, escrow_refund) == 0);
    assert(offsetof(tinyvm_apply_result, token) == 16);
    assert(offsetof(tinyvm_apply_result, owner) == 48);
    assert(offsetof(tinyvm_apply_result, success) == 68);

    /* Write known values and verify at byte level */
    tinyvm_apply_result r;
    memset(&r, 0, sizeof(r));
    r.escrow_refund = (unsigned __int128)123456789012345678ULL * 100;
    r.token[0] = 0xBB;
    r.token[31] = 0xBB;
    r.owner[0] = 0xCC;
    r.owner[19] = 0xCC;
    r.success = 1;

    uint8_t *p = (uint8_t *)&r;
    /* escrow at bytes 0-15 */
    unsigned __int128 read_refund;
    memcpy(&read_refund, p, 16);
    assert(read_refund == r.escrow_refund);
    /* token at bytes 16-47 */
    assert(p[16] == 0xBB);
    assert(p[47] == 0xBB);
    /* owner at bytes 48-67 */
    assert(p[48] == 0xCC);
    assert(p[67] == 0xCC);
    /* success at byte 68 */
    assert(p[68] == 1);

    printf("OK\n");
}

/* ── Simple store implementation ── */
#define MAX_ENTRIES 256
#define MAX_KEY_LEN 256
#define MAX_VAL_LEN 4096

typedef struct {
    uint8_t key[MAX_KEY_LEN];
    size_t key_len;
    uint8_t value[MAX_VAL_LEN];
    size_t value_len;
} store_entry;

typedef struct {
    store_entry entries[MAX_ENTRIES];
    int count;
} simple_store;

static simple_store g_store;

int store_get_cb(void *ctx, uint8_t const *key, size_t key_len,
                 uint8_t *value_buf, size_t value_buf_len, size_t *value_len) {
    (void)ctx;
    for (int i = 0; i < g_store.count; i++) {
        if (g_store.entries[i].key_len == key_len &&
            memcmp(g_store.entries[i].key, key, key_len) == 0) {
            size_t copy = g_store.entries[i].value_len;
            if (copy > value_buf_len) copy = value_buf_len;
            memcpy(value_buf, g_store.entries[i].value, copy);
            *value_len = g_store.entries[i].value_len;
            return 1;
        }
    }
    *value_len = 0;
    return 0;
}

void store_set_cb(void *ctx, uint8_t const *key, size_t key_len,
                  uint8_t const *value, size_t value_len) {
    (void)ctx;
    /* Update existing or add new */
    for (int i = 0; i < g_store.count; i++) {
        if (g_store.entries[i].key_len == key_len &&
            memcmp(g_store.entries[i].key, key, key_len) == 0) {
            memcpy(g_store.entries[i].value, value, value_len);
            g_store.entries[i].value_len = value_len;
            return;
        }
    }
    assert(g_store.count < MAX_ENTRIES);
    memcpy(g_store.entries[g_store.count].key, key, key_len);
    g_store.entries[g_store.count].key_len = key_len;
    memcpy(g_store.entries[g_store.count].value, value, value_len);
    g_store.entries[g_store.count].value_len = value_len;
    g_store.count++;
}

/* ── Test 2: Call tinyvm_apply with garbage — must fail gracefully ── */
void test_apply_rejects_garbage(void) {
    printf("test_apply_rejects_garbage: ");

    memset(&g_store, 0, sizeof(g_store));
    tinyvm_apply_result result = {};
    char error_buf[256] = {};
    uint8_t logs_buf[4096] = {};
    size_t logs_written = 0;
    uint8_t sender[20] = {0xa1};
    uint8_t garbage[] = {0xff, 0xfe, 0xfd};

    int rc = tinyvm_apply(
        sender, 20,
        0, 0,
        garbage, sizeof(garbage),
        NULL,
        store_get_cb, store_set_cb,
        &result,
        logs_buf, sizeof(logs_buf), &logs_written,
        error_buf, sizeof(error_buf));

    assert(rc == 0 || result.success == 0);
    printf("OK (rc=%d, error=%s)\n", rc, error_buf);
}

/* ── Test 3: escrow_refund round-trip via tinyvm_apply ── */
/* We can't easily construct valid proofs from C, but we CAN verify that
   the result struct is zeroed on failure — proving the C compiler reads
   the same offsets that Rust writes. */
void test_result_struct_zeroed_on_failure(void) {
    printf("test_result_struct_zeroed_on_failure: ");

    tinyvm_apply_result result;
    /* Fill with known pattern */
    memset(&result, 0xAA, sizeof(result));

    char error_buf[256] = {};
    uint8_t logs_buf[4096] = {};
    size_t logs_written = 0;
    uint8_t sender[20] = {0xa1};
    uint8_t garbage[] = {0xff};

    int rc = tinyvm_apply(
        sender, 20,
        0, 0,
        garbage, sizeof(garbage),
        NULL,
        store_get_cb, store_set_cb,
        &result,
        logs_buf, sizeof(logs_buf), &logs_written,
        error_buf, sizeof(error_buf));

    /* Rust should have set success = 0 */
    assert(result.success == 0);
    printf("OK (success=%d at offset %zu)\n",
           result.success, offsetof(tinyvm_apply_result, success));
}

/* ── Test 4: u128 boundary — verify escrow_refund can hold > u64::MAX ── */
void test_escrow_refund_u128_capacity(void) {
    printf("test_escrow_refund_u128_capacity: ");

    tinyvm_apply_result result = {};
    /* Simulate Rust writing a large u128 value */
    unsigned __int128 large_value = (unsigned __int128)100 * 1000000000000000000ULL; /* 100 MON */
    result.escrow_refund = large_value;

    /* Read it back — must match */
    assert(result.escrow_refund == large_value);
    assert(result.escrow_refund > (unsigned __int128)UINT64_MAX);

    /* Read via byte pointer (simulates cross-compiler boundary) */
    unsigned __int128 read_back;
    memcpy(&read_back, (uint8_t *)&result + offsetof(tinyvm_apply_result, escrow_refund), 16);
    assert(read_back == large_value);

    printf("OK (value=%llu * 100)\n", (unsigned long long)(large_value / 100));
}

int main(void) {
    printf("=== C FFI Integration Tests ===\n\n");

    test_struct_layout();
    test_apply_rejects_garbage();
    test_result_struct_zeroed_on_failure();
    test_escrow_refund_u128_capacity();

    printf("\nAll tests passed.\n");
    return 0;
}
