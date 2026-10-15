// Copyright (C) 2026 Category Labs, Inc.
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

// Bare-metal runtime for the Airbender guest: what ziskos supplies on ZisK
// and libzkevm.a on SP1. Entry and RAM setup, the eth-act IO ABI over
// Airbender's non-determinism CSR, a bump allocator, the mem* routines the
// compiler calls, and the Keccak-f the sponge in keccak_accel.cpp drives.
//
// Conventions are Airbender's (zksync-airbender riscv_common/src/lib.rs):
// a word of input is `csrrw rd, 0x7c0, x0`; a run ends by loading its output
// into x10..x25 and looping on itself; a failed run writes the read-only
// `cycle` CSR, which no proof can satisfy.

#include <stddef.h>
#include <stdint.h>

extern void monad_zkvm_execute_witness(void);

// Linker script symbols (link.x).
extern uint32_t _srodata[];
extern uint32_t _erodata[];
extern uint32_t const _sirodata[];
extern uint32_t _sdata[];
extern uint32_t _edata[];
extern uint32_t const _sidata[];
extern uint8_t _sheap[];
extern uint8_t _eheap[];
extern void (*__init_array_start[])(void);
extern void (*__init_array_end[])(void);

// ---- Termination ----

static uint32_t output_words[16];
static size_t output_size;

__attribute__((noreturn, noinline)) static void finish_success(void)
{
    // The base moves to x26 first: x10..x25 are the outputs the loads fill,
    // as in Airbender's own runtime.
    __asm__ volatile("mv x26, %0\n\t"
                     "lw x10, 0(x26)\n\t"
                     "lw x11, 4(x26)\n\t"
                     "lw x12, 8(x26)\n\t"
                     "lw x13, 12(x26)\n\t"
                     "lw x14, 16(x26)\n\t"
                     "lw x15, 20(x26)\n\t"
                     "lw x16, 24(x26)\n\t"
                     "lw x17, 28(x26)\n\t"
                     "lw x18, 32(x26)\n\t"
                     "lw x19, 36(x26)\n\t"
                     "lw x20, 40(x26)\n\t"
                     "lw x21, 44(x26)\n\t"
                     "lw x22, 48(x26)\n\t"
                     "lw x23, 52(x26)\n\t"
                     "lw x24, 56(x26)\n\t"
                     "lw x25, 60(x26)\n\t"
                     "1: j 1b"
                     :
                     : "r"(output_words)
                     : "memory");
    __builtin_unreachable();
}

__attribute__((noreturn, noinline)) static void finish_error(void)
{
    __asm__ volatile("csrrw x0, cycle, x0" ::: "memory");
    __builtin_unreachable();
}

// ---- Debug output over the quasi-UART ----
// A CSR write is a query to the host's oracle; the transpiler's source prints
// a run of them -- 0xffffffff, the word count, the byte length, the bytes as
// little-endian words -- as one `UART:` line.

static inline void uart_write_word(uint32_t const w)
{
    __asm__ volatile("csrrw x0, 0x7c0, %0" ::"r"(w));
}

void monad_zkvm_airbender_print(char const *const s, size_t const len)
{
    uart_write_word(0xffffffffu);
    uart_write_word((uint32_t)(1 + (len + 3) / 4));
    uart_write_word((uint32_t)len);
    for (size_t i = 0; i < len; i += 4) {
        uint32_t w = 0;
        for (size_t j = 0; j < 4 && i + j < len; ++j) {
            w |= (uint32_t)(uint8_t)s[i + j] << (8 * j);
        }
        uart_write_word(w);
    }
}

static void print_with_hex(char const *const what, uint32_t const v)
{
    char buf[64];
    size_t n = 0;
    while (what[n] && n < 40) {
        buf[n] = what[n];
        ++n;
    }
    buf[n++] = '0';
    buf[n++] = 'x';
    for (int k = 28; k >= 0; k -= 4) {
        buf[n++] = "0123456789abcdef"[(v >> k) & 0xf];
    }
    monad_zkvm_airbender_print(buf, n);
}

__attribute__((noreturn)) void zkvm_halt(int const status)
{
    if (status == 0) {
        finish_success();
    }
    print_with_hex("zkvm_halt status ", (uint32_t)status);
    print_with_hex("zkvm_halt called from ",
                   (uint32_t)(uintptr_t)__builtin_return_address(0));
    finish_error();
}

__attribute__((noreturn)) void abort(void)
{
    print_with_hex("abort called from ",
                   (uint32_t)(uintptr_t)__builtin_return_address(0));
    finish_error();
}

// ---- Entry ----

__attribute__((noreturn)) void monad_zkvm_airbender_start(void)
{
    // .rodata, .data and the RELRO sections live in RAM, their images in ROM;
    // link.x aligns each to 16 bytes, so whole words copy them.
    for (uint32_t *d = _srodata; d != _erodata; ++d) {
        *d = _sirodata[d - _srodata];
    }
    for (uint32_t *d = _sdata; d != _edata; ++d) {
        *d = _sidata[d - _sdata];
    }
    for (void (**f)(void) = __init_array_start; f != __init_array_end; ++f) {
        (*f)();
    }
    monad_zkvm_execute_witness();
    finish_success();
}

// ---- Allocator: a bump arena over the rest of RAM ----

static uintptr_t heap_next;

void *sys_alloc_aligned(size_t const size, size_t const align)
{
    if (heap_next == 0) {
        heap_next = (uintptr_t)_sheap;
    }
    uintptr_t const p = (heap_next + align - 1) & ~(uintptr_t)(align - 1);
    if (p + size < p || p + size > (uintptr_t)_eheap) {
        print_with_hex("out of heap, request ", (uint32_t)size);
        finish_error();
    }
    heap_next = p + size;
    return (void *)p;
}

// ---- eth-act IO ABI (zkvm_io.h) over the non-determinism CSR ----

static inline uint32_t csr_read_word(void)
{
    uint32_t w;
    __asm__ volatile("csrrw %0, 0x7c0, x0" : "=r"(w));
    return w;
}

// The host's oracle answers with the input's byte length, then its bytes as
// little-endian words, the last one zero-padded.
void read_input(uint8_t const **const buf_ptr, size_t *const buf_size)
{
    size_t const len = csr_read_word();
    uint32_t *const words = sys_alloc_aligned((len + 3) & ~(size_t)3, 4);
    for (size_t i = 0; i < (len + 3) / 4; ++i) {
        words[i] = csr_read_word();
    }
    *buf_ptr = (uint8_t const *)words;
    *buf_size = len;
}

// Appends to the 64 output bytes the run ends with; anything past them is
// dropped.
void write_output(uint8_t const *const output, size_t const size)
{
    uint8_t *const out = (uint8_t *)output_words;
    for (size_t i = 0; i < size && output_size < sizeof(output_words); ++i) {
        out[output_size++] = output[i];
    }
}

// ---- mem*: the compiler calls these; byte loops widened to aligned words ----

void *memcpy(void *const dst, void const *const src, size_t n)
{
    uint8_t *d = dst;
    uint8_t const *s = src;
    if ((((uintptr_t)d ^ (uintptr_t)s) & 3) == 0) {
        while (n && ((uintptr_t)d & 3)) {
            *d++ = *s++;
            --n;
        }
        for (; n >= 4; n -= 4, d += 4, s += 4) {
            *(uint32_t *)d = *(uint32_t const *)s;
        }
    }
    while (n--) {
        *d++ = *s++;
    }
    return dst;
}

void *memmove(void *const dst, void const *const src, size_t n)
{
    uint8_t *d = dst;
    uint8_t const *s = src;
    if (d == s || n == 0) {
        return dst;
    }
    if (d < s || d >= s + n) {
        return memcpy(dst, src, n);
    }
    while (n--) {
        d[n] = s[n];
    }
    return dst;
}

void *memset(void *const dst, int const c, size_t n)
{
    uint8_t *d = dst;
    uint32_t const w = 0x01010101u * (uint8_t)c;
    while (n && ((uintptr_t)d & 3)) {
        *d++ = (uint8_t)c;
        --n;
    }
    for (; n >= 4; n -= 4, d += 4) {
        *(uint32_t *)d = w;
    }
    while (n--) {
        *d++ = (uint8_t)c;
    }
    return dst;
}

int memcmp(void const *const a, void const *const b, size_t const n)
{
    uint8_t const *x = a;
    uint8_t const *y = b;
    for (size_t i = 0; i < n; ++i) {
        if (x[i] != y[i]) {
            return x[i] < y[i] ? -1 : 1;
        }
    }
    return 0;
}

size_t strlen(char const *const s)
{
    size_t n = 0;
    while (s[n]) {
        ++n;
    }
    return n;
}

// ---- Keccak-f[1600] ----
// Airbender's Keccak-f delegation (zksync-airbender common_constants
// delegation_types/keccak_f1600.rs): 361 CSR writes over a 256-byte-aligned
// block whose slots 0..24 hold the lanes in the standard x + 5y order and
// 25..29 the column parities. Per round, five column-parity (0x7cd), five
// theta/rho (0x7cc) and five chi (0x7ce) calls; a last column-parity call
// applies the delayed final iota. x10 starts at zero and the circuit steps
// it; x11 points at the block. The run must be one uninterrupted sequence,
// which the transpiler recognises by its first CSR and its length.
//
// MONAD_ZKVM_AIRBENDER_SOFT_KECCAK selects a software permutation instead.

#ifndef MONAD_ZKVM_AIRBENDER_SOFT_KECCAK

static uint64_t keccak_block[32] __attribute__((aligned(256)));

#define KECCAK_CALL(csr) "csrrw x0, " #csr ", x0\n\t"
#define KECCAK_5(csr)                                                          \
    KECCAK_CALL(csr) KECCAK_CALL(csr) KECCAK_CALL(csr) KECCAK_CALL(csr)       \
        KECCAK_CALL(csr)
#define KECCAK_ROUND KECCAK_5(0x7cd) KECCAK_5(0x7cc) KECCAK_5(0x7ce)
#define KECCAK_4_ROUNDS KECCAK_ROUND KECCAK_ROUND KECCAK_ROUND KECCAK_ROUND
#define KECCAK_24_ROUNDS                                                       \
    KECCAK_4_ROUNDS KECCAK_4_ROUNDS KECCAK_4_ROUNDS KECCAK_4_ROUNDS            \
        KECCAK_4_ROUNDS KECCAK_4_ROUNDS

void monad_zkvm_airbender_keccak_f1600(uint64_t (*const state)[25])
{
    uint64_t *const st = *state;
    for (unsigned i = 0; i < 25; ++i) {
        keccak_block[i] = st[i];
    }
    __asm__ volatile("mv x11, %0\n\t"
                     "add x10, x0, x0\n\t" KECCAK_24_ROUNDS KECCAK_CALL(0x7cd)
                     :
                     : "r"(keccak_block)
                     : "x10", "x11", "memory");
    for (unsigned i = 0; i < 25; ++i) {
        st[i] = keccak_block[i];
    }
}

#else

#define ROTL64(x, y) (((x) << (y)) | ((x) >> (64 - (y))))

static uint64_t const keccak_rc[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
    0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
    0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
    0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
    0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL};
static uint8_t const keccak_rotc[24] = {1,  3,  6,  10, 15, 21, 28, 36,
                                        45, 55, 2,  14, 27, 41, 56, 8,
                                        25, 43, 62, 18, 39, 61, 20, 44};
static uint8_t const keccak_piln[24] = {10, 7,  11, 17, 18, 3,  5,  16,
                                        8,  21, 24, 4,  15, 23, 19, 13,
                                        12, 2,  20, 14, 22, 9,  6,  1};

void monad_zkvm_airbender_keccak_f1600(uint64_t (*const state)[25])
{
    uint64_t *const st = *state;
    uint64_t bc[5];
    for (unsigned r = 0; r < 24; ++r) {
        for (unsigned i = 0; i < 5; ++i) {
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        }
        for (unsigned i = 0; i < 5; ++i) {
            uint64_t const t =
                bc[(i + 4) % 5] ^ ROTL64(bc[(i + 1) % 5], 1);
            for (unsigned j = 0; j < 25; j += 5) {
                st[j + i] ^= t;
            }
        }
        uint64_t t = st[1];
        for (unsigned i = 0; i < 24; ++i) {
            unsigned const j = keccak_piln[i];
            uint64_t const next = st[j];
            st[j] = ROTL64(t, keccak_rotc[i]);
            t = next;
        }
        for (unsigned j = 0; j < 25; j += 5) {
            for (unsigned i = 0; i < 5; ++i) {
                bc[i] = st[j + i];
            }
            for (unsigned i = 0; i < 5; ++i) {
                st[j + i] ^= ~bc[(i + 1) % 5] & bc[(i + 2) % 5];
            }
        }
        st[0] ^= keccak_rc[r];
    }
}

#endif // MONAD_ZKVM_AIRBENDER_SOFT_KECCAK
