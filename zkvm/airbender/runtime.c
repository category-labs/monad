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

// The mem* loops below must stay loops: gcc would otherwise recognise them as
// memcpy/memset and call the function being defined. And memcpy stays whole:
// split, its fast paths would call the rest with a frame.
#pragma GCC optimize("no-tree-loop-distribute-patterns", "no-partial-inlining")

extern void monad_zkvm_execute_witness(void);
extern void monad_zkvm_run_precompile_tests(void);
void monad_zkvm_airbender_memstats_print(void);

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
#ifdef MONAD_ZKVM_AIRBENDER_PRECOMPILE_TESTS
static uint8_t report[512];
static size_t report_size;
#endif

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
#ifdef MONAD_ZKVM_AIRBENDER_SOFT_HALT
    // Diagnostic: a failed run ends in the success loop instead, its outputs
    // 0xdead, so that the runner's profiles and transcript are still written.
    output_words[0] = 0xdead;
    finish_success();
#else
    __asm__ volatile("csrrw x0, cycle, x0" ::: "memory");
    __builtin_unreachable();
#endif
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
#ifdef MONAD_ZKVM_AIRBENDER_PRECOMPILE_TESTS
    // The golden-vector guest (zkvm/test/precompile_tests); its report, longer
    // than the 64 output bytes, also goes over the quasi-UART as hex.
    monad_zkvm_run_precompile_tests();
    {
        static char const hex[] = "0123456789abcdef";
        char line[2 * 64];
        for (size_t i = 0; i < report_size; i += 64) {
            size_t n = 0;
            for (size_t j = i; j < report_size && j < i + 64; ++j) {
                line[n++] = hex[report[j] >> 4];
                line[n++] = hex[report[j] & 15];
            }
            monad_zkvm_airbender_print(line, n);
        }
    }
#else
    monad_zkvm_execute_witness();
#endif
#ifdef MONAD_ZKVM_AIRBENDER_MEMSTATS
    monad_zkvm_airbender_memstats_print();
#endif
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
    // 8-aligned: an input lays codes out in place for the 8-byte boundaries
    // of their addresses (execute_witness.cpp), which then are the input's.
    uint32_t *const words = sys_alloc_aligned((len + 3) & ~(size_t)3, 8);
    // Eight words a turn: a turn per word also steps and tests, which on a
    // 7.5 MB witness (1.9M words) was half the loop's cycles.
    size_t const n = (len + 3) / 4;
    size_t i = 0;
    for (; i + 8 <= n; i += 8) {
        uint32_t *const w = words + i;
        w[0] = csr_read_word();
        w[1] = csr_read_word();
        w[2] = csr_read_word();
        w[3] = csr_read_word();
        w[4] = csr_read_word();
        w[5] = csr_read_word();
        w[6] = csr_read_word();
        w[7] = csr_read_word();
    }
    for (; i < n; ++i) {
        words[i] = csr_read_word();
    }
    *buf_ptr = (uint8_t const *)words;
    *buf_size = len;
}

// Appends to the 64 output bytes the run ends with; anything past them is
// dropped.
void write_output(uint8_t const *const output, size_t const size)
{
#ifdef MONAD_ZKVM_AIRBENDER_PRECOMPILE_TESTS
    for (size_t i = 0; i < size && report_size < sizeof(report); ++i) {
        report[report_size++] = output[i];
    }
#endif
#ifdef MONAD_ZKVM_AIRBENDER_DUMP_OUTPUT
    // Diagnostic: every output byte over the quasi-UART as hex, for outputs
    // past the registers' 64 bytes (e.g. MONAD_ZKVM_KECCAK_SITES counters).
    {
        static char const hex[] = "0123456789abcdef";
        char line[136];
        for (size_t at = 0; at < size; at += 64) {
            size_t n = 0;
            line[n++] = 'o';
            line[n++] = 'u';
            line[n++] = 't';
            line[n++] = ' ';
            for (size_t i = at; i < size && i < at + 64; ++i) {
                line[n++] = hex[output[i] >> 4];
                line[n++] = hex[output[i] & 15];
            }
            monad_zkvm_airbender_print(line, n);
        }
    }
#endif
    uint8_t *const out = (uint8_t *)output_words;
    for (size_t i = 0; i < size && output_size < sizeof(output_words); ++i) {
        out[output_size++] = output[i];
    }
}

// ---- mem*: the compiler calls these ----
// No unaligned access is provable, so every word access is aligned: a copy
// aligns its destination, then moves words, shift-combining two aligned
// source words when the source sits at another offset (each aligned word read
// holds at least one byte that is copied). Measured on block 25993213 before:
// 430K memcpy calls, 72% of them 9-32 bytes and aligned, and ~80K at
// different alignments, the multi-kilobyte ones bytewise.

#ifdef MONAD_ZKVM_AIRBENDER_MEMSTATS
// Diagnostic: calls by function, size class and alignment class, printed over
// the quasi-UART when the run ends.
static uint32_t memstats[3][8][3];
static uint32_t memstat_bytes[3][8][3];
static inline void
memstat(int const fn, size_t const n, uintptr_t const a, uintptr_t const b)
{
    int const sc = n == 0      ? 0
                   : n <= 8    ? 1
                   : n <= 20   ? 2
                   : n <= 32   ? 3
                   : n <= 64   ? 4
                   : n <= 256  ? 5
                   : n <= 4096 ? 6
                               : 7;
    int const al = ((a | b) & 3) == 0 ? 0 : ((a ^ b) & 3) == 0 ? 1 : 2;
    ++memstats[fn][sc][al];
    memstat_bytes[fn][sc][al] += n;
}

// Calls and bytes by call site (return address) and alignment class, in an
// open-addressed table; sites past its size are dropped.
#define MEMSITES 4096
static struct
{
    uintptr_t site;
    uint32_t fn;
    uint32_t calls[3];
    uint32_t bytes[3];
} memsites[MEMSITES];

static inline void memsite(
    int const fn, uintptr_t const site, size_t const n, uintptr_t const a,
    uintptr_t const b)
{
    int const al = ((a | b) & 3) == 0 ? 0 : ((a ^ b) & 3) == 0 ? 1 : 2;
    uint32_t h = (uint32_t)(site * 2654435761u) % MEMSITES;
    for (int probe = 0; probe < MEMSITES; ++probe, h = (h + 1) % MEMSITES) {
        if (memsites[h].site == site || memsites[h].site == 0) {
            memsites[h].site = site;
            memsites[h].fn = (uint32_t)fn;
            ++memsites[h].calls[al];
            memsites[h].bytes[al] += (uint32_t)n;
            return;
        }
    }
}

static void print_u32(char *const buf, size_t *const n, uint32_t v, int const base)
{
    char tmp[12];
    int k = 0;
    do {
        uint32_t const d = v % (uint32_t)base;
        tmp[k++] = (char)(d < 10 ? '0' + d : 'a' + d - 10);
        v /= (uint32_t)base;
    } while (v);
    while (k) {
        buf[(*n)++] = tmp[--k];
    }
}

static void memsites_print(void)
{
    char buf[160];
    for (int i = 0; i < MEMSITES; ++i) {
        if (memsites[i].site == 0) {
            continue;
        }
        size_t n = 0;
        static char const head[] = "memsite ";
        for (char const *c = head; *c; ++c) {
            buf[n++] = *c;
        }
        print_u32(buf, &n, memsites[i].fn, 10);
        buf[n++] = ' ';
        print_u32(buf, &n, (uint32_t)memsites[i].site, 16);
        for (int al = 0; al < 3; ++al) {
            buf[n++] = ' ';
            print_u32(buf, &n, memsites[i].calls[al], 10);
        }
        for (int al = 0; al < 3; ++al) {
            buf[n++] = ' ';
            print_u32(buf, &n, memsites[i].bytes[al], 10);
        }
        monad_zkvm_airbender_print(buf, n);
    }
}

void monad_zkvm_airbender_memstats_print(void)
{
    memsites_print();
    char buf[200];
    static char const *const fns[3] = {"memcpy", "memset", "memcmp"};
    for (int f = 0; f < 3; ++f) {
        for (int sc = 0; sc < 8; ++sc) {
            size_t n = 0;
            for (char const *c = fns[f]; *c; ++c) {
                buf[n++] = *c;
            }
            buf[n++] = ' ';
            buf[n++] = (char)('0' + sc);
            for (int al = 0; al < 6; ++al) {
                uint32_t v = al < 3 ? memstats[f][sc][al]
                                    : memstat_bytes[f][sc][al - 3];
                char tmp[12];
                int k = 0;
                buf[n++] = ' ';
                do {
                    tmp[k++] = (char)('0' + v % 10);
                    v /= 10;
                } while (v);
                while (k) {
                    buf[n++] = tmp[--k];
                }
            }
            monad_zkvm_airbender_print(buf, n);
        }
    }
}
    #define MEMSTAT(fn, n, a, b)                                               \
        (memstat(fn, n, (uintptr_t)(a), (uintptr_t)(b)),                       \
         memsite(                                                              \
             fn,                                                               \
             (uintptr_t)__builtin_return_address(0),                           \
             n,                                                                \
             (uintptr_t)(a),                                                   \
             (uintptr_t)(b)))
#else
    #define MEMSTAT(fn, n, a, b) ((void)0)
#endif

static inline uint32_t load32(uint8_t const *const p)
{
    return *(uint32_t const *)(void const *)p;
}

static inline void store32(uint8_t *const p, uint32_t const v)
{
    *(uint32_t *)(void *)p = v;
}

// Different offsets in a word: bytes up to the destination's word boundary,
// then each destination word shifted together from two aligned source words
// (each holds at least one byte that is copied), then the bytes left. A step
// loads one word and stores one: the barrier after it keeps gcc from loading
// a run of words ahead, which takes more registers than the steps need (it
// saved and restored five s-registers a call).
#define MONAD_COPY_STEP(K)                                                     \
    do {                                                                       \
        uint32_t const h = load32(w + 4 * (K) + 4);                            \
        store32(d + 4 * (K), (lo >> rs) | (h << ls));                          \
        lo = h;                                                                \
        __asm__ volatile("" ::: "memory");                                     \
    }                                                                          \
    while (0)

__attribute__((noinline)) static void *
copy_shifted(void *const dst, uint8_t *d, uint8_t const *s, size_t n)
{
    if (n < 8) {
        while (n--) {
            *d++ = *s++;
        }
        return dst;
    }
    while ((uintptr_t)d & 3) {
        *d++ = *s++;
        --n;
    }
    unsigned const off = (uintptr_t)s & 3;
    unsigned const rs = 8 * off;
    unsigned const ls = 32 - rs;
    uint8_t const *w = s - off;
    uint32_t lo = load32(w);
    for (; n >= 16; n -= 16, d += 16, w += 16) {
        MONAD_COPY_STEP(0);
        MONAD_COPY_STEP(1);
        MONAD_COPY_STEP(2);
        MONAD_COPY_STEP(3);
    }
    if (n & 8) {
        MONAD_COPY_STEP(0);
        MONAD_COPY_STEP(1);
        d += 8;
        w += 8;
    }
    if (n & 4) {
        MONAD_COPY_STEP(0);
        d += 4;
        w += 4;
    }
    s = w + off;
    for (n &= 3; n; --n) {
        *d++ = *s++;
    }
    return dst;
}

#undef MONAD_COPY_STEP

// Both word-aligned: eight words at a time, then what is left by its bits.
__attribute__((noinline)) static void *
copy_aligned(void *const dst, uint8_t *d, uint8_t const *s, size_t n)
{
    for (; n >= 32; n -= 32, d += 32, s += 32) {
        uint32_t const w0 = load32(s), w1 = load32(s + 4), w2 = load32(s + 8),
                       w3 = load32(s + 12), w4 = load32(s + 16), w5 = load32(s + 20),
                       w6 = load32(s + 24), w7 = load32(s + 28);
        store32(d, w0);
        store32(d + 4, w1);
        store32(d + 8, w2);
        store32(d + 12, w3);
        store32(d + 16, w4);
        store32(d + 20, w5);
        store32(d + 24, w6);
        store32(d + 28, w7);
    }
    if (n & 16) {
        uint32_t const w0 = load32(s), w1 = load32(s + 4), w2 = load32(s + 8),
                       w3 = load32(s + 12);
        store32(d, w0);
        store32(d + 4, w1);
        store32(d + 8, w2);
        store32(d + 12, w3);
        d += 16;
        s += 16;
    }
    if (n & 8) {
        uint32_t const w0 = load32(s), w1 = load32(s + 4);
        store32(d, w0);
        store32(d + 4, w1);
        d += 8;
        s += 8;
    }
    if (n & 4) {
        store32(d, load32(s));
        d += 4;
        s += 4;
    }
    if (n & 2) {
        *(uint16_t *)(void *)d = *(uint16_t const *)(void const *)s;
        d += 2;
        s += 2;
    }
    if (n & 1) {
        *d = *s;
    }
    return dst;
}

// A copy's fixed cost is most of it: on block 25993213, 230K of the 427K calls
// copy 32 aligned bytes (a word or a hash) and 71K copy 20 (an address), where
// the bytes the bulk copies move cost a cycle or two each whatever is done.
// Both sizes go straight through, with no frame; the rest tail-call a copy by
// words, after the bytes up to a word boundary when source and destination
// share an offset in a word, or by shifted words when they do not.
void *memcpy(void *const dst, void const *const src, size_t n)
{
    MEMSTAT(0, n, dst, src);
    uint8_t *d = dst;
    uint8_t const *s = src;
    if ((((uintptr_t)d | (uintptr_t)s) & 3) == 0) {
        if (n == 32) {
            uint32_t const w0 = load32(s), w1 = load32(s + 4), w2 = load32(s + 8),
                           w3 = load32(s + 12), w4 = load32(s + 16), w5 = load32(s + 20),
                           w6 = load32(s + 24), w7 = load32(s + 28);
            store32(d, w0);
            store32(d + 4, w1);
            store32(d + 8, w2);
            store32(d + 12, w3);
            store32(d + 16, w4);
            store32(d + 20, w5);
            store32(d + 24, w6);
            store32(d + 28, w7);
            return dst;
        }
        if (n == 20) {
            uint32_t const w0 = load32(s), w1 = load32(s + 4), w2 = load32(s + 8),
                           w3 = load32(s + 12), w4 = load32(s + 16);
            store32(d, w0);
            store32(d + 4, w1);
            store32(d + 8, w2);
            store32(d + 12, w3);
            store32(d + 16, w4);
            return dst;
        }
        return copy_aligned(dst, d, s, n);
    }
    if ((((uintptr_t)d ^ (uintptr_t)s) & 3) != 0) {
        return copy_shifted(dst, d, s, n);
    }
    while ((uintptr_t)d & 3) {
        if (n == 0) {
            return dst;
        }
        *d++ = *s++;
        --n;
    }
    return copy_aligned(dst, d, s, n);
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
    // Backwards, by words when both ends share an alignment.
    d += n;
    s += n;
    if ((((uintptr_t)d ^ (uintptr_t)s) & 3) == 0) {
        while (n && ((uintptr_t)d & 3)) {
            *--d = *--s;
            --n;
        }
        for (; n >= 4; n -= 4) {
            d -= 4;
            s -= 4;
            store32(d, load32(s));
        }
    }
    while (n--) {
        *--d = *--s;
    }
    return dst;
}

void *memset(void *const dst, int const c, size_t n)
{
    MEMSTAT(1, n, dst, dst);
    uint8_t *d = dst;
    uint8_t const b = (uint8_t)c;
    if (n < 8) {
        while (n--) {
            *d++ = b;
        }
        return dst;
    }
    uint32_t const w = 0x01010101u * b;
    while ((uintptr_t)d & 3) {
        *d++ = b;
        --n;
    }
    for (; n >= 32; n -= 32, d += 32) {
        store32(d, w);
        store32(d + 4, w);
        store32(d + 8, w);
        store32(d + 12, w);
        store32(d + 16, w);
        store32(d + 20, w);
        store32(d + 24, w);
        store32(d + 28, w);
    }
    for (; n >= 4; n -= 4, d += 4) {
        store32(d, w);
    }
    while (n--) {
        *d++ = b;
    }
    return dst;
}

int memcmp(void const *const a, void const *const b, size_t n)
{
    MEMSTAT(2, n, a, b);
    uint8_t const *x = a;
    uint8_t const *y = b;
    // Nearly every call compares a 20- or 32-byte key at word-aligned
    // addresses, after its hash matched: equal, which the OR of the words'
    // differences tells with no branch a word. A difference goes on to the
    // word loop, and the bytes order it.
    if ((((uintptr_t)x | (uintptr_t)y) & 3) == 0) {
        if (n == 20) {
            uint32_t const diff = (load32(x) ^ load32(y)) |
                                  (load32(x + 4) ^ load32(y + 4)) |
                                  (load32(x + 8) ^ load32(y + 8)) |
                                  (load32(x + 12) ^ load32(y + 12)) |
                                  (load32(x + 16) ^ load32(y + 16));
            if (diff == 0) {
                return 0;
            }
        }
        else if (n == 32) {
            uint32_t const diff = (load32(x) ^ load32(y)) |
                                  (load32(x + 4) ^ load32(y + 4)) |
                                  (load32(x + 8) ^ load32(y + 8)) |
                                  (load32(x + 12) ^ load32(y + 12)) |
                                  (load32(x + 16) ^ load32(y + 16)) |
                                  (load32(x + 20) ^ load32(y + 20)) |
                                  (load32(x + 24) ^ load32(y + 24)) |
                                  (load32(x + 28) ^ load32(y + 28));
            if (diff == 0) {
                return 0;
            }
        }
        for (; n >= 4; n -= 4, x += 4, y += 4) {
            if (load32(x) != load32(y)) {
                break;
            }
        }
    }
    for (; n; --n, ++x, ++y) {
        if (*x != *y) {
            return *x < *y ? -1 : 1;
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

// The block itself, for a sponge that keeps its state there (keccak_accel.cpp).
uint64_t (*monad_zkvm_airbender_keccak_state(void))[25]
{
    return (uint64_t (*)[25])keccak_block;
}

static inline void keccak_block_permute(void)
{
    __asm__ volatile("mv x11, %0\n\t"
                     "add x10, x0, x0\n\t" KECCAK_24_ROUNDS KECCAK_CALL(0x7cd)
                     :
                     : "r"(keccak_block)
                     : "x10", "x11", "memory");
}

void monad_zkvm_airbender_keccak_f1600(uint64_t (*const state)[25])
{
    uint64_t *const st = *state;
    if (st == keccak_block) {
        keccak_block_permute();
        return;
    }
    for (unsigned i = 0; i < 25; ++i) {
        keccak_block[i] = st[i];
    }
    keccak_block_permute();
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
