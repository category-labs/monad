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

// keccak256 for the zkVM guests, entered directly at the permutation
// precompile -- one word-wise sponge, two syscall doors.
//
// zisklib's wrapper assembles the sponge state BYTE BY BYTE — its
// disassembly is 137 lbu / 119 slli / 119 or per iteration group — which
// costs ~400-530 steps of marshalling around every keccak_f invocation.
// This entry absorbs word-wise: 17 ld+xor on an aligned block, shift-combine
// on a misaligned one (aligned reads only, never past the input), and the tail
// goes through ZisK's emulator-accelerated memcpy.
//
// The permutation itself, the padding rule (0x01 domain, 0x80 close — the
// Ethereum keccak, not SHA-3) and the 136-byte rate are identical to
// zisklib's; only the marshalling differs.

// SP1's wrapper has the same disease in a different coat: zkvm_keccak256 is
// tiny_keccak's sponge in software (only keccak-f reaches the KECCAK_PERMUTE
// precompile), absorbing byte by byte -- measured at 19.5 % of the SP1 guest's
// attributed work, because the pre-state binding hashes the whole witness trie.

#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_SP1)

#include <category/core/likely.h>

#include <cstddef>
#include <cstdint>
#include <cstring>

#include <zkvm/guest/known_inputs.hpp>

// An unaligned 8-byte load. The memcpy is the portable spelling of one; gcc
// folds it into a single instruction.
[[gnu::always_inline]] static inline uint64_t
load64(unsigned char const *const p)
{
    uint64_t v;
    __builtin_memcpy(&v, p, sizeof v);
    return v;
}

#ifdef MONAD_ZKVM_ZISK
// ziskos's raw precompile entry (no_mangle, extern "C"), the same door
// zisklib's own wrapper uses.
extern "C" void syscall_keccak_f(uint64_t (*state)[25]);

// ziskos' `syscall_keccak_f` is two instructions -- `csrs 0x800, a0` and the
// return -- so the call costs more than the body: a `jal` in at 68 cells and a
// `jalr` out at 68 plus the 60 its low-bit `and` is priced at, 196 cells on each
// of the block's 97,918 permutations. Emitted here it is the one instruction.
//
// The form is ziskos' own (`ziskos_syscall!(SYSCALL_KECCAKF_ID, state)` expands
// to `csrs {port}, {value}`, and the transpiler shows it as `keccak 0, rs`).
// rd = x0 is correct for THIS port; it is not for add256, where the same
// spelling silently transpiles to an `or` -- see zisk_add256.
//
// Safe against the memo's ordering requirement. What that requires is that no
// OTHER Keccak-f run between `fcall_set_keccakf_index` and this permutation, and
// the compiler cannot introduce one; `asm volatile` statements are not reordered
// against each other, and the "memory" clobber keeps the state's stores and loads
// on the correct side.
[[gnu::always_inline]] inline void zisk_keccakf(uint64_t (*state)[25]) noexcept
{
    asm volatile(".option push\n\t"
                 ".option arch, +zicsr\n\t"
                 "csrs 0x800, %0\n\t"
                 ".option pop"
                 :
                 : "r"(state)
                 : "memory");
}

// Keccak-f memo. OFF gives the exact control arm: the mechanism is compiled
// out, not disabled, so an A/B measures the memo rather than a predicate.
#ifndef MONAD_ZKVM_KECCAKF_MEMO
    #define MONAD_ZKVM_KECCAKF_MEMO 1
#endif

#if MONAD_ZKVM_KECCAKF_MEMO

// ── the permutation memo ─────────────────────────────────────────────────
//
// A permutation is 38,454 of ZisK cost against 15-60 for an ordinary op, and
// keccak is 24.4 % of this guest's COST -- both on ziskemu 1.2. About 14 % of
// the permutations a block runs repeat a state an earlier one already
// permuted.
//
// What makes the memo pay is that the LOOKUP is not in the proof. The guest
// does not hash the state; it asks the executor, which keeps the same map
// natively (zisk-core `opc_fcall`, plus the assembly emulator's copy in
// zisk-lib-c, so the prover's EXECUTE phase knows it too). `fcall_param`,
// `fcall` and `fcall_get` all cost ZERO in `zisk_ops_costs.rs`. A guest-side
// fingerprint over the 25 words was measured at +9.09 % COST on 1.1, where a
// permutation was priced at twice what 1.2 charges, so the margin against
// fingerprinting is wider than that figure. Avoiding it is the whole reason
// this is worth building.
//
// SOUNDNESS. The index is a HINT: a free-input call is not verified by the
// VM, and a wrong or hostile answer must not be able to change a digest. Two
// checks make that so, and neither trusts the executor:
//
//   1. the index must be below `keccakf_memo_used`, i.e. inside the part of
//      the table THIS execution has written. That also subsumes the
//      not-found sentinel, which is ~0 and so never in range;
//   2. the entry it points at must hold THIS state, compared word for word.
//
// Only then is its output used, and that output was produced by this same
// execution running the real permutation. Keccak-f is a function, so equal
// inputs have equal outputs: a bad hint costs a wasted compare and never a
// wrong answer. `keccakf_memo_used` moves only after both halves of an entry
// are written, so an index that arrives early is still out of range.
//
// The entry owns the bytes it compares against. Keying on the caller's
// pointer would be unsound — the sponge permutes a stack buffer the next
// call reuses, so a later state landing at the same address would compare
// equal to a stale entry and take an output computed from bytes long gone.
constexpr size_t KECCAKF_LANES = 25;
constexpr size_t KECCAKF_STATE_BYTES = KECCAKF_LANES * sizeof(uint64_t);

// One entry per DISTINCT state, appended in first-permuted order; the index
// the executor returns is a position in here. No sets, no ways, no eviction
// — the executor's map is exact, so the guest side needs no geometry and
// every distinct state that fits gets a slot instead of fighting for one.
//
// 2^18 x 400 B = 100 MiB of .bss, sized against the worst block on record
// rather than the median: 234,215 permutations (block 25552366), of which
// ~86 % carry a state not seen before, so ~201 k distinct. ZisK gives the
// guest 512 MB and this guest's measured peak is 42.5 MB on 25815091, so the
// table fits with room. Above capacity it stops growing, which costs proving
// speed and never correctness.
// Padded to a power of two. Two states are 400 bytes, and 400 is not a shift:
// indexing the table costs a `mul` per permutation for `[index].in` and
// another for `[used]`, 108,946 executions a block at 97 cells each where a
// `slli` is 56. The padding is never read or written -- `keccakf_state_eq` and
// `keccakf_state_copy` both work in lanes -- and costs 28 MiB of .bss on a
// table that already holds 100 of a 512 MB budget.
struct alignas(8) KeccakfEntry
{
    uint64_t in[KECCAKF_LANES]; // the state before the permutation
    uint64_t out[KECCAKF_LANES]; // and after it
    uint64_t pad[64 - 2 * KECCAKF_LANES];
};

static_assert(
    sizeof(KeccakfEntry) == 512 && sizeof(KeccakfEntry) > 2 * KECCAKF_STATE_BYTES,
    "an entry is the two states, padded to a shift");

constexpr size_t KECCAKF_MEMO_ENTRIES = size_t{1} << 18;

// The memo's globals, gathered in one object that `gp` points at. The guest's
// RAM sits above 2^31, so a plain global costs an `auipc` and its low 12 bits
// on every access, and the "memory" clobber of every fcall and permutation
// makes gcc form the address again after each one. Neither linker relaxes
// those pairs to `gp`, which ziskos sets in `_start` and nothing reads after.
// Held in `gp` instead, the apart state is `gp` itself, the count is one load
// or store at a fixed offset, and an entry is its index's shift and one add.
// The table is last so that every other field's offset fits a load's 12 bits.
struct alignas(8) KeccakfHot
{
    // The state a digest's unfiled permutations run in, apart from the
    // scratch slot: a trie node's last one under Filing::NotFinal, and all of
    // them under Filing::None. Every lane is written before each permutation
    // but the first block's capacity, which None clears first, so nothing is
    // cleared after it, where the scratch would be cleared whole.
    uint64_t keccakf_apart[KECCAKF_LANES];

    uint64_t keccakf_memo_used;

    // The first of keccakf_fresh_states that no digest has stood on, and one
    // past the last of them: see keccak256_one_block_fresh. Set by the
    // constructor below; after it, the cursor only ever advances.
    uint64_t *keccakf_fresh;
    uint64_t *keccakf_fresh_end;

    // One entry past capacity. `keccakf_memo[keccakf_memo_used]` is the
    // scratch a one-block digest builds its state in (keccak256_one_block
    // below), and `keccakf_memo_used` reaches KECCAKF_MEMO_ENTRIES when the
    // table fills, so the slot has to exist for the sponge to have somewhere
    // to stand. It is never filed and never in range: 512 B of .bss for one
    // fewer bounds branch on the hot path.
    KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES + 1];
};

static_assert(
    offsetof(KeccakfHot, keccakf_memo) + offsetof(KeccakfEntry, out) +
            KECCAKF_STATE_BYTES <=
        2048,
    "an entry's two states are reached at a 12-bit offset from gp");

// Zero-initialised .bss, so the table's untouched slots still read zero as
// the one-block scratch requires, and no constructor runs for it.
static KeccakfHot keccakf_hot;

// The states keccak256_one_block_fresh permutes a trie node's one block in,
// each handed out once, from the front. Zero-initialised .bss like the table,
// and nothing writes a state before it is handed out, so each reads zero as
// the table's untouched slots do. 2^15 states are 6.25 MiB; a digest that
// finds them all used takes the memo's one-block path, so the count bounds
// only how many go unfiled.
constexpr size_t KECCAKF_FRESH_STATES = size_t{1} << 15;
static uint64_t keccakf_fresh_states[KECCAKF_FRESH_STATES * KECCAKF_LANES];

// `gp` is a fixed register to gcc, so no code of this guest -- C++, ziskos'
// Rust or the libraries -- allocates it, and setting it here takes it from
// nobody. Nothing writes it after the constructor below, so every function
// reads the same base out of the register and none has to form it.
register KeccakfHot *hot asm("gp");

// Points `gp` at the memo before anything can hash. A priority constructor
// runs ahead of every default-priority one, all of which ziskos' _zisk_main
// runs before it enters the guest, so no static initialiser that hashes and
// no part of the entry ever sees `gp` still at _global_pointer, nor the fresh
// states' cursor unset.
[[gnu::constructor(101)]] static void keccakf_hot_init()
{
    hot = &keccakf_hot;
    hot->keccakf_fresh = keccakf_fresh_states;
    hot->keccakf_fresh_end =
        keccakf_fresh_states + KECCAKF_FRESH_STATES * KECCAKF_LANES;
}

// A 200-byte block op that reaches the DMA port instead of being expanded
// inline. gcc turns a constant-size copy into 25 ld/sd pairs — 50
// instructions AND the same 50 memory accesses the port pays — where the
// port is one op plus those accesses. This is the call the rate loop below
// says would be worth having and could not get; hiding the length behind an
// empty asm is what forces it, and here there is no surrounding work for the
// constant to fold into.
//
// Under -mzisk-dma the constant is what you want instead: the backend lowers
// a constant-size block move to the port INLINE, so the same port op arrives
// without the call, the frame or the a0/a1/a2 marshalling. Hiding the length
// there would give up the lowering and keep the call. MONAD_ZKVM_ZISK_DMA_LOWERING
// is set by the same CMake option that adds the flag, so the two never drift.
#ifdef MONAD_ZKVM_ZISK_DMA_LOWERING
    #define MONAD_KECCAKF_LEN(n) (n)
#else
static inline size_t keccakf_opaque(size_t n)
{
    asm("" : "+r"(n));
    return n;
}
    #define MONAD_KECCAKF_LEN(n) keccakf_opaque(n)
#endif

static inline bool keccakf_state_eq(uint64_t const *a, uint64_t const *b)
{
    return std::memcmp(a, b, MONAD_KECCAKF_LEN(KECCAKF_STATE_BYTES)) == 0;
}

static inline void keccakf_state_copy(uint64_t *dst, uint64_t const *src)
{
    std::memcpy(dst, src, MONAD_KECCAKF_LEN(KECCAKF_STATE_BYTES));
}

// The two free-input calls, in the encoding ziskos' fcall macros produce:
//
//   csrs  0x8F0+p, rs1   push a parameter; p selects the word count, 0 = the
//                        register value itself, 8 = the 25 words at that
//                        address
//   csrwi 0x8C0, id      run fcall `id` over the parameters pushed
//   csrr  rd,  0xFFE     read the next result word
//
// The parameter is any register, as ziskos' fcall macros take it (`in(reg)`).
// It must not be x0 -- the transpiler reads `csrrs x0, csr, x0` as a nop
// instead of a parameter push, and the fcall would silently see no arguments
// -- and a plain "r" never is: x0 is a fixed register, which gcc prints only
// for a "J" constant under %z; a constant zero is loaded into a register
// first. Pinned to a0, the parameter cost a move into a0 before most pushes.
// `_zicsr` is already in the guest's -march, which is what lets these
// assemble at all.
constexpr uint64_t KECCAKF_INDEX_NOT_FOUND = ~uint64_t{0};

// File the input state of the NEXT permutation under `index`.
static inline void fcall_set_keccakf_index(uint64_t const index)
{
    asm volatile("csrs 0x8F0, %0\n\t" // one parameter, by value
                 "csrwi 0x8C0, 24" // FCALL_SET_KECCAKF_CACHE_INDEX_ID
                 :
                 : "r"(index)
                 : "memory");
}

// The index `state` was filed under, or KECCAKF_INDEX_NOT_FOUND.
static inline uint64_t fcall_get_keccakf_index(uint64_t const *const state)
{
    uint64_t index;
    asm volatile("csrs 0x8F8, %[st]\n\t" // one parameter: 25 words at [st]
                 "csrwi 0x8C0, 25\n\t" // FCALL_GET_KECCAKF_CACHE_INDEX_ID
                 "csrr %[idx], 0xFFE" // fcall_get: the index
                 : [idx] "=&r"(index)
                 : [st] "r"(state)
                 : "memory");
    return index;
}

// A digest whose whole input fits in one rate block -- 33,123 of this guest's
// 47,455 memoised calls on block 25815042 -- never needs the state to outlive
// its single permutation. So it builds the padded block IN the slot the memo
// would file it under, and the miss path's copy of the pre-state disappears:
// the pre-state is already where the entry wants it. Two 200-byte port copies
// become one on a miss and none on a hit, 1,232 cells either way.
//
// SOUNDNESS. Both of the memo's checks are here, unchanged and in the same
// order, and neither trusts the executor: the hint must be below
// `keccakf_memo_used`, and the entry it names must hold this state word for
// word. The scratch is `keccakf_memo[keccakf_memo_used]`, which is not below
// `keccakf_memo_used`, so it can never be served as its own hint; and
// `keccakf_memo_used` still moves only after both halves of the entry are
// written, so an index that arrives early is still out of range. A hit leaves
// the scratch unpublished, for the next call to overwrite. `keccak_permute`'s
// note on why an entry must own the bytes it compares against holds here too:
// the entry owns them, the caller's buffer is never keyed on.
//
// The scratch is all zero on entry, so the block is built without clearing it
// first. Every slot past `keccakf_memo_used` is untouched, and untouched memory
// reads zero on ZisK: the memory AIR constrains a first read to 0. A miss
// publishes this slot, so the next call stands on a fresh one; a hit clears
// the lanes the block's builder wrote before it returns; and the spare past a
// full table, the one slot reused as it is, is permuted in place and cleared
// whole before the call returns.
//
// This is the half after the padded pre-state is built, shared by the
// runtime-length builder and the constant-length entries below. `Lanes` is how
// many leading lanes the builder may have written; a hit clears those and lane
// 16, which every builder writes. No permutation ran in the slot on a hit, so
// every other lane is still zero.
template <size_t Lanes>
[[gnu::always_inline]] static inline void keccak256_one_block_finish(
    KeccakfEntry &e, uint64_t const used, uint8_t out[32])
{
    static_assert(Lanes >= 1 && Lanes <= 17);
    uint64_t *const s = e.in;

    uint64_t const index = fcall_get_keccakf_index(s);
    if (index < used && keccakf_state_eq(hot->keccakf_memo[index].in, s)) {
        std::memcpy(out, hot->keccakf_memo[index].out, 32);
        std::memset(s, 0, Lanes * sizeof(uint64_t));
        if constexpr (Lanes < 17) {
            s[16] = 0;
        }
        return;
    }

    if (used == KECCAKF_MEMO_ENTRIES) {
        // Full: keep permuting, stop remembering. The scratch is the spare
        // slot, so permute it in place, then clear all of it for the next.
        zisk_keccakf(&e.in);
        std::memcpy(out, s, 32);
        std::memset(s, 0, KECCAKF_STATE_BYTES);
        return;
    }

    // `in` holds the pre-state already. Stage the copy the permutation will
    // consume, then keep the request and the permutation adjacent for the
    // reason `keccak_permute` gives. The rate alone: a one-block pre-state's
    // capacity is zero, and so is this slot's `out`, which nothing writes
    // before the slot is published.
    std::memcpy(e.out, s, 17 * sizeof(uint64_t));
    fcall_set_keccakf_index(used);
    zisk_keccakf(&e.out);
    // Published last: this is what puts the entry in range, so it must not
    // move until both halves are there.
    hot->keccakf_memo_used = used + 1;
    std::memcpy(out, e.out, 32);
}

static void keccak256_one_block(
    void const *const in, size_t const len, uint8_t out[32])
{
    static_assert(135 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");

    // Read once: an fcall or a permutation is an asm statement that may touch
    // any memory, so gcc reads the global again after each of them, and the
    // entry's address with it.
    uint64_t const used = hot->keccakf_memo_used;
    KeccakfEntry &e = hot->keccakf_memo[used];
    uint64_t *const s = e.in;

    if (len) {
        std::memcpy(s, in, len);
    }
    reinterpret_cast<unsigned char *>(s)[len] = 0x01;
    s[16] |= uint64_t{0x80} << 56;

    // Lanes 0-16, the rate: the block wrote bytes 0..len and byte 135.
    keccak256_one_block_finish<17>(e, used, out);
}

// The same digest for a length known at compile time -- an address, a key, a
// public key -- entered from monad_keccak256 when the caller's length folds to
// a constant. The constant takes out what only a runtime length needs: the
// one-block-or-sponge test, the length handed to the block copy, and the
// read-modify-write of lane 16.
//
// The scratch is zero on entry (see keccak256_one_block_finish), so the pad
// stores below write into zero bytes. The 0x01 goes in whole when it starts a
// lane, and as a byte otherwise, since the lane's low bytes are input. Lane 16
// can take the 0x80 as a plain store only while no input or 0x01 byte reaches
// it, that is N + 1 <= 128; at N = 135 the two pad bytes share byte 135 and
// the lane would need 0x81.
template <size_t N>
static void keccak256_one_block_n(void const *const in, uint8_t out[32])
{
    static_assert(135 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    static_assert(N >= 1 && N + 1 <= 16 * 8, "lane 16 holds only the pad bit");

    uint64_t const used = hot->keccakf_memo_used;
    KeccakfEntry &e = hot->keccakf_memo[used];
    uint64_t *const s = e.in;

    std::memcpy(s, in, N);
    if constexpr (N % 8 == 0) {
        s[N / 8] = 0x01;
    }
    else {
        reinterpret_cast<unsigned char *>(s)[N] = 0x01;
    }
    s[16] = uint64_t{0x80} << 56;

    // The input and the 0x01 span the first (N + 1 + 7) / 8 lanes.
    keccak256_one_block_finish<(N + 1 + 7) / 8>(e, used, out);
}

// A trie node's digest of one rate block, which the memo neither asks after
// nor files. Its hint almost never comes: the post-state hashes such a node
// again only where it changed, and a node of the pre-state seldom repeats one
// hashed before it. So keccak256_one_block's miss is what it pays nearly every
// time -- the hint request and its range test, the rate's copy into the
// entry's `out`, the filing and the count's store -- for a hit that rarely
// saves a permutation. Here the block is built in a state no digest has stood
// on, and permuted in place.
//
// The state is zero on entry, as keccak256_one_block's scratch is: the cursor
// only advances, so no state is handed out twice and none was written before.
// The block is built the way keccak256_one_block builds it.
//
// SOUNDNESS. Nothing here comes from the executor. Not filing can only cost a
// later digest its hint; and without `fcall_set_keccakf_index` the executor
// may file this permutation under a stale index, which the compare rejects --
// a lost hint, never a wrong digest (see monad_zkvm_keccak256_fast_nomemo).
// Once the fresh states are used up, the digest takes keccak256_one_block,
// the memo's two checks with it.
static void keccak256_one_block_fresh(
    void const *const in, size_t const len, uint8_t out[32])
{
    static_assert(135 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");

    uint64_t *const s = hot->keccakf_fresh;
    if (MONAD_UNLIKELY(s == hot->keccakf_fresh_end)) {
        keccak256_one_block(in, len, out);
        return;
    }
    hot->keccakf_fresh = s + KECCAKF_LANES;

    if (len) {
        std::memcpy(s, in, len);
    }
    reinterpret_cast<unsigned char *>(s)[len] = 0x01;
    s[16] |= uint64_t{0x80} << 56;
    zisk_keccakf(reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(s));
    std::memcpy(out, s, 32);
}

// One permutation of the pre-state standing in the scratch slot,
// `keccakf_memo[keccakf_memo_used].in`, with the memo's two checks in their
// usual order; returns where the post-state lies. A hit names an earlier entry,
// whose `out` is the post-state and is never written again, and leaves the
// scratch holding the pre-state. A miss copies the scratch's `in` to its `out`,
// permutes that, and publishes the slot. A full table permutes the spare the
// same way without filing it. `First`: the sponge's first block, whose
// capacity is zero, so a miss copies the rate alone -- the slot's `out` is
// zero too, nothing writing it before the slot is published. The spare's is
// not, and it gets the whole state. Without `Lookup` the pre-state is filed and
// permuted without the hint request: the miss a caller knows it has.
//
// A miss returns the slot's own `out`, `pre + KECCAKF_LANES`, and a hit an
// earlier entry's: the caller tells the two apart by that address.
//
// `used` is the caller's copy of `keccakf_memo_used`, held for the whole
// digest and stored back at its end, for the reason keccak256_one_block
// gives; the slot's `out` is reached from `pre`, which the caller launders.
// With `Room` the caller has shown the table holds an entry for every
// permutation its digest can still file, so the full-table arm is left out.
template <bool First, bool Lookup = true, bool Room = false>
static inline uint64_t const *
keccakf_memo_permute(uint64_t *const pre, uint64_t &used)
{
    if constexpr (Lookup) {
        uint64_t const index = fcall_get_keccakf_index(pre);
        if (index < used &&
            keccakf_state_eq(hot->keccakf_memo[index].in, pre)) {
            return hot->keccakf_memo[index].out;
        }
    }
    uint64_t *const slot_out = pre + KECCAKF_LANES;
    auto *const post = reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(slot_out);
    if constexpr (!Room) {
        if (used == KECCAKF_MEMO_ENTRIES) {
            keccakf_state_copy(slot_out, pre);
            zisk_keccakf(post);
            return slot_out;
        }
    }
    if constexpr (First) {
        std::memcpy(slot_out, pre, 17 * sizeof(uint64_t));
    }
    else {
        keccakf_state_copy(slot_out, pre);
    }
    // Adjacent, for the reason `keccak_permute` gives.
    fcall_set_keccakf_index(used);
    zisk_keccakf(post);
    // Published last, as in `keccak_permute`.
    ++used;
    return slot_out;
}

// One permutation of the pre-state standing in the scratch slot that files
// nothing: a hit (with `Lookup`) names an earlier entry's `out`, as
// keccakf_memo_permute's does; otherwise the scratch is permuted in place and
// returned, and stays unpublished for the next digest to overwrite. Without
// `fcall_set_keccakf_index` the executor may file this permutation under a
// stale index, which the compare rejects: a lost hint, never a wrong digest
// (see monad_zkvm_keccak256_fast_nomemo).
template <bool Lookup>
static inline uint64_t const *
keccakf_unfiled_permute(uint64_t *const pre, uint64_t const used, bool &hit)
{
    if constexpr (Lookup) {
        uint64_t const index = fcall_get_keccakf_index(pre);
        if (index < used &&
            keccakf_state_eq(hot->keccakf_memo[index].in, pre)) {
            hit = true;
            return hot->keccakf_memo[index].out;
        }
    }
    hit = false;
    zisk_keccakf(reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(pre));
    return pre;
}

// Which permutations of a digest of a rate block or more the memo files.
// `All`: every one. `NotFinal`: all but the last, for an input whose whole
// repeats are rare but whose leading blocks a later digest may share -- a
// trie node, which the post-state hashes again with some children changed;
// the last permutation's output is the digest itself. `None`: none, for that
// later digest: the requests hit until the first change, and nothing after
// will be asked for again.
enum class Filing
{
    All,
    NotFinal,
    None
};

// A digest of a rate block or more, built the way keccak256_one_block builds
// one: each block's pre-state goes straight into the scratch slot the memo
// would file it under, made from the previous post-state where that already
// lies -- the entry a miss just published, or the one a hit named -- and the
// block. Against a state kept on the stack, a miss copies one state instead of
// two and a hit copies none, for a 64-byte copy of the capacity into each block
// after the first: 12 of the 25 lanes' worth of port traffic saved or more.
//
// The scratch is zero on entry, which the first block relies on for its
// capacity; every later block writes all 25 lanes. When the last permutation
// leaves the scratch where it was -- a hit, or the spare of a full table -- it
// is cleared before the call returns, so the next digest finds it zero too.
// The permutations no entry is filed for run in keccakf_apart instead, which
// is never assumed zero: Filing::None's whole chain, its capacity cleared
// first, and NotFinal's last block whenever the scratch was left clean.
//
// `From` is where the blocks are read from, which the caller decides: the
// input itself when it is 8-byte aligned; an aligned copy of it when it is not
// and fits one, as the stack sponge stages it -- every lane would otherwise be
// a boundary-crossing load, 159 against 16; and the misaligned input itself
// when it is longer. Deciding it here instead would put a call in this
// function's rare path, and gcc then copies all three arguments out of their
// registers on entry, on every path.
enum class MemoFrom
{
    Aligned,
    Staged,
    Misaligned
};

constexpr size_t MEMO_STAGED_BYTES = 8 * 136;

// Where the sponge starts: at the input's first block; there too, leaving a
// mark of where the memo filed the states after the input's whole blocks; or
// from such a state, `post`, the input then being what follows its blocks.
//
// A mark is the first block's slot plus one, written only when that block was
// filed. A prime asks for no hint: its first block is filed as a miss, and
// every later block but the last is filed in the next slot -- the
// straight-line full-branch tail and the Room loop alike -- until the table
// fills: the state after block j is at mark - 1 + j, if that is below
// `keccakf_memo_used`. A first block the full table permuted in its spare
// files nothing, and leaves no mark. Prime goes with Filing::NotFinal, whose
// whole blocks are all filed, and Resume with Filing::None, the post-state's.
enum class SpongeEntry
{
    Plain,
    Prime,
    Resume
};

// The one argument a prime (the mark's address) or a resume (its state) takes
// past `used`. A plain sponge takes none: a null argument would be one more
// register to set before the jump to it, on every input of a block or more.
template <typename T>
[[gnu::always_inline]] static inline T sponge_extra(T const extra)
{
    return extra;
}

// `used` is the caller's load of `keccakf_memo_used`, stored back once, at the
// end: see keccakf_memo_permute. `Room` is the caller's one test that the table
// has an entry for every permutation this digest files (keccak256_memo_digest
// below). With it no permutation tests for a full table, and the slot a filing
// leaves is always the next one: the no-lookup loop steps its slot pointer
// instead of re-forming it from `used`, and the scratch is left in use only
// where no filing followed it. Without it, every filing keeps its test.
template <
    MemoFrom From, Filing F, bool Room,
    SpongeEntry Entry = SpongeEntry::Plain, typename... Extra>
static void keccak256_memo_sponge(
    void const *const in, size_t len, uint8_t out[32], uint64_t used,
    [[maybe_unused]] Extra const... extra)
{
    constexpr size_t RATE = 136;
    constexpr size_t WORDS = RATE / 8; // 17
    static_assert(135 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    static_assert(!Room || F != Filing::None, "None files nothing");
    static_assert(Entry != SpongeEntry::Prime || F == Filing::NotFinal);
    static_assert(Entry != SpongeEntry::Resume || F == Filing::None);
    auto const *p = static_cast<unsigned char const *>(in);

    [[maybe_unused]] alignas(8) unsigned char staged[MEMO_STAGED_BYTES];
    if constexpr (From == MemoFrom::Staged) {
        std::memcpy(staged, p, len);
        p = staged;
    }

    uint64_t *pre;
    uint64_t const *post;
    bool look;
    if constexpr (Entry == SpongeEntry::Resume) {
        // From a filed state, with lookups on: a patched ref that holds the
        // hash it held when primed leaves the next block as the prime filed
        // it. The lookup loop below takes a whole block's capacity from that
        // state, and the final block takes it there too. Not the full-branch
        // tail, which starts after a first-block miss.
        pre = hot->keccakf_apart;
        post = sponge_extra(extra...);
        look = true;
    }
    else {
        pre = hot->keccakf_memo[used].in;
        if constexpr (F == Filing::None) {
            pre = hot->keccakf_apart;
            std::memset(pre + WORDS, 0, (KECCAKF_LANES - WORDS) * 8);
        }
        std::memcpy(pre, p, RATE);
        p += RATE;
        len -= RATE;
        if constexpr (F == Filing::None) {
            post = keccakf_unfiled_permute<true>(pre, used, look);
        }
        else if constexpr (Entry == SpongeEntry::Prime) {
            // A primed node's first block is almost never one the memo holds:
            // it is filed as a miss, without the hint request, and lookups are
            // off from the start, so that none of the sponge's lookup arms is
            // built. A state the table already held is filed again, which a
            // later hint's word-for-word compare does not mind.
            uint64_t const first = used;
            post = keccakf_memo_permute<true, false, Room>(pre, used);
            look = false;
            // The count moves only when the block is filed.
            if (used != first) {
                *sponge_extra(extra...) = used;
            }
        }
        else {
            post = keccakf_memo_permute<true, true, Room>(pre, used);
            look = post != pre + KECCAKF_LANES;
        }
    }

    // A branch node with all sixteen children hashed is 532 bytes of RLP (a
    // 3-byte list header, sixteen 33-byte references and the empty value),
    // and it is most of what reaches this sponge from the trie. After a
    // first-block miss its other 396 bytes are always two middle blocks and a
    // final block of fifteen lanes and four bytes, so they are absorbed here
    // in straight-line code: literal offsets from one base, no per-block
    // length or table-full test, no jump table and no masked or shifted read
    // for the partial lane. Each filing does what the no-lookup path does,
    // block for block: All files all three, NotFinal the two middle blocks
    // and permutes the last one apart, None files none and permutes all three
    // in keccakf_apart, where its first block's miss left the state. A filed
    // slot's input is complete before it is copied, filed and permuted, and
    // the count is published once at the end. The room test asks for every
    // filed slot below capacity, which a first block run in the full table's
    // spare fails; such digests take the general path below. The hint on the
    // miss keeps gcc from carrying `look` into that path as a value, which a
    // first-block hit would otherwise pay for in extra steps.
    constexpr size_t FULL_BRANCH = 532;
    static_assert(
        FULL_BRANCH - RATE == 2 * RATE + 15 * 8 + 4,
        "two middle blocks, then fifteen lanes and four bytes");
    if constexpr (F == Filing::None && Entry != SpongeEntry::Resume) {
        if (MONAD_LIKELY(!look) && len == FULL_BRANCH - RATE) {
            // The miss permuted keccakf_apart in place: `post` is `pre`.
            uint64_t *st = pre;
            asm("" : "+r"(st));
            auto *const perm = reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(st);
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= load64(p + 8 * i);
            }
            zisk_keccakf(perm);
            unsigned char const *const q1 = p + RATE;
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= load64(q1 + 8 * i);
            }
            zisk_keccakf(perm);
            unsigned char const *const q2 = p + 2 * RATE;
            for (size_t i = 0; i < 15; ++i) {
                st[i] ^= load64(q2 + 8 * i);
            }
            // The input's last four bytes, read in place: an eight-byte load
            // at this lane would run four bytes past the input. The domain
            // byte follows them, and the closing bit is the top of lane 16.
            uint32_t last;
            __builtin_memcpy(&last, q2 + 15 * 8, sizeof last);
            st[15] ^= last | uint64_t{0x01} << 32;
            st[16] ^= uint64_t{0x80} << 56;
            zisk_keccakf(perm);
            // Nothing filed and the scratch untouched: `used` stands.
            std::memcpy(out, st, 32);
            return;
        }
    }
    else if constexpr (F != Filing::None) {
        constexpr uint64_t FILED = F == Filing::All ? 3 : 2;
        if (MONAD_LIKELY(!look) && len == FULL_BRANCH - RATE &&
            used + FILED <= KECCAKF_MEMO_ENTRIES) {
            // One opaque base for the slots keeps every lane at a literal
            // offset from a single register.
            KeccakfEntry *e = &hot->keccakf_memo[used];
            asm("" : "+r"(e));
            for (size_t i = 0; i < WORDS; ++i) {
                e[0].in[i] = post[i] ^ load64(p + 8 * i);
            }
            std::memcpy(
                e[0].in + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
            keccakf_state_copy(e[0].out, e[0].in);
            fcall_set_keccakf_index(used);
            zisk_keccakf(&e[0].out);

            unsigned char const *const q1 = p + RATE;
            for (size_t i = 0; i < WORDS; ++i) {
                e[1].in[i] = e[0].out[i] ^ load64(q1 + 8 * i);
            }
            std::memcpy(
                e[1].in + WORDS, e[0].out + WORDS, (KECCAKF_LANES - WORDS) * 8);
            keccakf_state_copy(e[1].out, e[1].in);
            fcall_set_keccakf_index(used + 1);
            zisk_keccakf(&e[1].out);

            // NotFinal's last block is not filed: it is built and permuted
            // apart, and the scratch is left as the filings left it, unwritten.
            uint64_t *const fin =
                F == Filing::All ? e[2].in : hot->keccakf_apart;
            unsigned char const *const q2 = p + 2 * RATE;
            for (size_t i = 0; i < 15; ++i) {
                fin[i] = e[1].out[i] ^ load64(q2 + 8 * i);
            }
            // The input's last four bytes, read in place: an eight-byte load
            // at this lane would run four bytes past the input. The domain
            // byte follows them, and the closing bit is the top of lane 16.
            uint32_t last;
            __builtin_memcpy(&last, q2 + 15 * 8, sizeof last);
            fin[15] = e[1].out[15] ^ (last | uint64_t{0x01} << 32);
            fin[16] = e[1].out[16] ^ (uint64_t{0x80} << 56);
            std::memcpy(
                fin + WORDS, e[1].out + WORDS, (KECCAKF_LANES - WORDS) * 8);
            if constexpr (F == Filing::All) {
                keccakf_state_copy(e[2].out, e[2].in);
                fcall_set_keccakf_index(used + 2);
                zisk_keccakf(&e[2].out);
                std::memcpy(out, e[2].out, 32);
            }
            else {
                zisk_keccakf(reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(fin));
                std::memcpy(out, fin, 32);
            }
            // Every block but NotFinal's last was filed, so the next scratch
            // is a slot no one has written.
            hot->keccakf_memo_used = used + FILED;
            return;
        }
    }

    // From the first miss, every later pre-state of this input is new as well:
    // a block xors into the rate alone, so one of them could be filed only if an
    // earlier permutation's output had the capacity of this one's, whose input
    // was never filed. The blocks after a miss are filed without the hint
    // request, three steps and a priced range test each: two in three of the
    // sponge's requests.
    while (look && len >= RATE) {
        pre =
            F == Filing::None ? hot->keccakf_apart : hot->keccakf_memo[used].in;
        // Opaque, so that the lanes are reached at offsets from it: seen
        // through, gcc forms each lane's address from the table's base in a
        // register of its own, ten of them saved and restored on entry.
        asm("" : "+r"(pre));
        for (size_t i = 0; i < WORDS; ++i) {
            pre[i] = post[i] ^ load64(p + 8 * i);
        }
        std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        if constexpr (F == Filing::None) {
            post = keccakf_unfiled_permute<true>(pre, used, look);
        }
        else {
            post = keccakf_memo_permute<false, true, Room>(pre, used);
            look = post != pre + KECCAKF_LANES;
        }
        p += RATE;
        len -= RATE;
    }
    if constexpr (Room) {
        // Every permutation from here files at `pre` and advances `used` by
        // one, so the next scratch is the entry after `pre`. While `look`
        // holds every permutation so far hit, and `pre` is still the scratch.
        constexpr size_t SLOT = sizeof(KeccakfEntry) / sizeof(uint64_t);
        if (!look) {
            while (len >= RATE) {
                pre += SLOT;
                asm("" : "+r"(pre));
                for (size_t i = 0; i < WORDS; ++i) {
                    pre[i] = post[i] ^ load64(p + 8 * i);
                }
                std::memcpy(
                    pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
                post = keccakf_memo_permute<false, false, true>(pre, used);
                p += RATE;
                len -= RATE;
            }
            if constexpr (F == Filing::All) {
                pre += SLOT;
            }
        }
    }
    else {
        while (len >= RATE) {
            pre = F == Filing::None ? hot->keccakf_apart
                                    : hot->keccakf_memo[used].in;
            asm("" : "+r"(pre));
            for (size_t i = 0; i < WORDS; ++i) {
                pre[i] = post[i] ^ load64(p + 8 * i);
            }
            if constexpr (F == Filing::None) {
                // The scratch was permuted in place: the capacity is
                // already there.
                bool hit;
                post = keccakf_unfiled_permute<false>(pre, used, hit);
            }
            else {
                std::memcpy(
                    pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
                post = keccakf_memo_permute<false, false>(pre, used);
            }
            p += RATE;
            len -= RATE;
        }
    }

    // The final block, pad10*1 with the 0x01 domain byte: its whole lanes, a
    // literal count per case; then its last partial lane; then the lanes it
    // leaves as they were. Read aligned, the partial lane is the word that
    // holds it, the bytes past the input's end masked off: the load stays in
    // the aligned word holding the input's last byte, which the region holding
    // the input holds whole -- RAM and ROM are word-granular, and an input
    // record is padded to eight bytes. Read misaligned, it is the eight bytes
    // that END at the input's end, shifted down, in bounds since a whole block
    // came before -- a boundary-crossing load, like every lane of such an input.
    //
    // A node's last block, which NotFinal does not file, is built and permuted
    // apart when the filed blocks left the scratch clean -- the last of them a
    // miss, which published its slot -- so nothing is cleared after it. A hit
    // left its pre-state in the scratch, and a full table permutes the spare
    // where it lies: those build the last block there and clear it, as before.
    // None ran every block apart.
    //
    // With Room the scratch is `pre` already, and every filing went below
    // capacity: NotFinal builds its last block apart after any miss.
    if constexpr (F == Filing::NotFinal) {
        if constexpr (Room) {
            if (!look) {
                pre = hot->keccakf_apart;
            }
        }
        else {
            pre = !look && used != KECCAKF_MEMO_ENTRIES
                      ? hot->keccakf_apart
                      : hot->keccakf_memo[used].in;
        }
    }
    else if constexpr (F == Filing::None) {
        pre = hot->keccakf_apart;
    }
    else if constexpr (!Room) {
        pre = hot->keccakf_memo[used].in;
    }
    size_t const whole = len / 8;
    unsigned const rem = static_cast<unsigned>(len % 8);
    // Entered through a table of the cases' addresses, not a switch: gcc's
    // jump table holds 4-byte offsets from its base, read by a lw -- a
    // sub-word ROM read ZisK prices at 120 cells, sign-extended -- and added
    // to that base, behind a bound test. Each entry here is one aligned 8-byte
    // read, and `whole` needs no bound: len < RATE after the loop.
    static void *const entry[] = {
        &&lanes0,  &&lanes1,  &&lanes2,  &&lanes3,  &&lanes4,  &&lanes5,
        &&lanes6,  &&lanes7,  &&lanes8,  &&lanes9,  &&lanes10, &&lanes11,
        &&lanes12, &&lanes13, &&lanes14, &&lanes15, &&lanes16};
    static_assert(sizeof(entry) / sizeof(entry[0]) == WORDS);
    goto *entry[whole];
lanes16:
    pre[15] = post[15] ^ load64(p + 120);
lanes15:
    pre[14] = post[14] ^ load64(p + 112);
lanes14:
    pre[13] = post[13] ^ load64(p + 104);
lanes13:
    pre[12] = post[12] ^ load64(p + 96);
lanes12:
    pre[11] = post[11] ^ load64(p + 88);
lanes11:
    pre[10] = post[10] ^ load64(p + 80);
lanes10:
    pre[9] = post[9] ^ load64(p + 72);
lanes9:
    pre[8] = post[8] ^ load64(p + 64);
lanes8:
    pre[7] = post[7] ^ load64(p + 56);
lanes7:
    pre[6] = post[6] ^ load64(p + 48);
lanes6:
    pre[5] = post[5] ^ load64(p + 40);
lanes5:
    pre[4] = post[4] ^ load64(p + 32);
lanes4:
    pre[3] = post[3] ^ load64(p + 24);
lanes3:
    pre[2] = post[2] ^ load64(p + 16);
lanes2:
    pre[1] = post[1] ^ load64(p + 8);
lanes1:
    pre[0] = post[0] ^ load64(p);
lanes0:
    uint64_t lane = uint64_t{0x01} << (8 * rem);
    if (rem != 0) {
        if constexpr (From != MemoFrom::Misaligned) {
            lane |= load64(p + 8 * whole) & (lane - 1);
        }
        else {
            lane |= load64(p + len - 8) >> (8 * (8 - rem));
        }
    }
    pre[whole] = post[whole] ^ lane;
    if (F != Filing::None || post != pre) {
        std::memcpy(
            pre + whole + 1, post + whole + 1, (KECCAKF_LANES - 1 - whole) * 8);
    }
    pre[16] ^= uint64_t{0x80} << 56;
    if constexpr (Room) {
        // A filing advances `used` past `pre`, to an unwritten slot: the
        // scratch is left in use only by a final hit, or, under NotFinal, by
        // the hits that kept the last block in it, and only those clear it.
        if constexpr (F == Filing::All) {
            if (look) {
                post = keccakf_memo_permute<false, true, true>(pre, used);
                if (post != pre + KECCAKF_LANES) {
                    std::memcpy(out, post, 32);
                    std::memset(pre, 0, KECCAKF_STATE_BYTES);
                    hot->keccakf_memo_used = used;
                    return;
                }
            }
            else {
                post = keccakf_memo_permute<false, false, true>(pre, used);
            }
            std::memcpy(out, post, 32);
        }
        else {
            bool hit;
            post = keccakf_unfiled_permute<false>(pre, used, hit);
            std::memcpy(out, post, 32);
            if (look) {
                std::memset(pre, 0, KECCAKF_STATE_BYTES);
            }
        }
        hot->keccakf_memo_used = used;
        return;
    }
    if constexpr (F == Filing::All) {
        post = look ? keccakf_memo_permute<false>(pre, used)
                    : keccakf_memo_permute<false, false>(pre, used);
    }
    else if constexpr (F == Filing::NotFinal) {
        bool hit;
        post = keccakf_unfiled_permute<false>(pre, used, hit);
    }
    else {
        bool hit;
        post = look ? keccakf_unfiled_permute<true>(pre, used, hit)
                    : keccakf_unfiled_permute<false>(pre, used, hit);
    }
    std::memcpy(out, post, 32);

    if (pre == hot->keccakf_memo[used].in) {
        std::memset(pre, 0, KECCAKF_STATE_BYTES);
    }
    hot->keccakf_memo_used = used;
}

// The table's room, tested once per digest rather than at every permutation.
// An input of len >= 136 bytes takes len / 136 + 1 <= (len >> 7) + 1
// permutations, and each files at most one entry, so when
// `used + (len >> 7) < KECCAKF_MEMO_ENTRIES` every filing lands below the
// table's capacity and the scratch the digest ends on is at worst the spare
// slot, which exists. A hit or an unfiled permutation files nothing, so the
// bound only over-counts. Filing::None files nothing at all and never tests.
template <
    MemoFrom From, Filing F = Filing::All,
    SpongeEntry Entry = SpongeEntry::Plain, typename... Extra>
[[gnu::always_inline]] static inline void keccak256_memo_digest(
    void const *const in, size_t const len, uint8_t out[32],
    Extra const... extra)
{
    uint64_t const used = hot->keccakf_memo_used;
    if constexpr (F != Filing::None) {
        if (used + (len >> 7) < KECCAKF_MEMO_ENTRIES) {
            keccak256_memo_sponge<From, F, true, Entry>(
                in, len, out, used, extra...);
            return;
        }
    }
    keccak256_memo_sponge<From, F, false, Entry>(in, len, out, used, extra...);
}

#endif // MONAD_ZKVM_KECCAKF_MEMO

// Only `syscall_keccak_f` above and the entry points below carry C linkage;
// everything between them is C++ and the sponge is a template, which may not have it.

// The only Keccak-f this guest runs. With the memo on it IS the permutation,
// with an earlier identical one reused when the executor knows of one.
//
// `Memo` is a template parameter and not a flag, because a flag would cost a
// load and a branch on all 120,701 permutations of a block. The sponge below
// is templated with it for the same reason.
template <bool Memo>
static inline void keccak_permute(uint64_t (*state)[25])
{
#if MONAD_ZKVM_KECCAKF_MEMO
    if constexpr (!Memo) {
        zisk_keccakf(state);
        return;
    }
    uint64_t *const s = &(*state)[0];
    // Read once, for the reason keccak256_one_block gives.
    uint64_t const used = hot->keccakf_memo_used;
    uint64_t const index = fcall_get_keccakf_index(s);

    // Cheap check first, so an out-of-range index — which is what
    // KECCAKF_INDEX_NOT_FOUND is — never reaches the compare.
    if (index < used && keccakf_state_eq(hot->keccakf_memo[index].in, s)) {
        keccakf_state_copy(s, hot->keccakf_memo[index].out);
        return;
    }

    if (used == KECCAKF_MEMO_ENTRIES) {
        // Full: keep permuting, stop remembering. Filing more would mean
        // evicting, and an evicted slot only ever produces hints that fail
        // the compare above.
        zisk_keccakf(state);
        return;
    }

    // Nothing may come between the request and the permutation: the executor
    // files whichever Keccak-f runs next, and this binary has a second one --
    // zisklib's own keccak256, 154 permutations a block on the ecrecover
    // path. A stray permutation in between would file the wrong state under
    // this index. The compare above would reject the resulting hint, so it is
    // a poisoned entry rather than a wrong digest, but keep these adjacent.
    KeccakfEntry &e = hot->keccakf_memo[used];
    keccakf_state_copy(e.in, s);
    fcall_set_keccakf_index(used);
    zisk_keccakf(state);
    keccakf_state_copy(e.out, s);
    // Published last: this is what puts the entry in range, so it must not
    // move until both halves are there.
    hot->keccakf_memo_used = used + 1;
#else
    zisk_keccakf(state);
#endif
}
#else
// SP1's syscall_keccak_permute symbol is LTO-internalised inside libzkevm.a,
// so emit the ecall the SDK itself emits: t0 = KECCAK_PERMUTE (0x00_01_01_09),
// a0 = state, a1 = 0. The precompile rewrites the 25 u64 lanes in place.
template <bool>
static inline void keccak_permute(uint64_t (*state)[25])
{
    register uintptr_t a0 asm("a0") = reinterpret_cast<uintptr_t>(state);
    register uintptr_t a1 asm("a1") = 0;
    register uint32_t t0 asm("t0") = 0x00010109u;
    asm volatile("ecall" : "+r"(a0) : "r"(t0), "r"(a1) : "memory");
}
#endif

// `Prefix` sends only the first `memo_blocks` rate blocks through the memo and
// the rest past it, for an input that shares a prefix with another: the stack
// sponge's memo, which copies the state in and out, on those blocks only.
template <bool Memo, bool Prefix = false>
static void keccak256_sponge(
    void const *const in, size_t len, uint8_t out[32],
    [[maybe_unused]] size_t memo_blocks = 0)
{
    constexpr size_t RATE = 136;
    constexpr size_t WORDS = RATE / 8; // 17

#if defined(MONAD_ZKVM_ZISK) && MONAD_ZKVM_KECCAKF_MEMO
    // 69.8 % of this entry's calls are one rate block (33,123 of 47,455 on
    // 25815042 -- a key, an address, a leaf or extension node's RLP). They
    // have a cheaper shape than the general sponge; see keccak256_one_block.
    if constexpr (Memo) {
        if (len < RATE) {
            keccak256_one_block(in, len, out);
        }
        else if ((reinterpret_cast<uintptr_t>(in) & 7) == 0) {
            keccak256_memo_digest<MemoFrom::Aligned>(in, len, out);
        }
        else if (len <= MEMO_STAGED_BYTES) {
            keccak256_memo_digest<MemoFrom::Staged>(in, len, out);
        }
        else {
            keccak256_memo_digest<MemoFrom::Misaligned>(in, len, out);
        }
        return;
    }
#endif

#ifdef MONAD_ZKVM_ZISK
    // The capacity, lanes 17 to 24, starts at zero, and only the permutation
    // writes it. The rate is cleared only for an input shorter than a block:
    // a longer one's first block is copied over the whole rate below.
    uint64_t st[25];
    std::memset(st + WORDS, 0, sizeof(st) - RATE);
    if (len < RATE) {
        std::memset(st, 0, RATE);
    }
#else
    uint64_t st[25] = {};
#endif
    auto const *p = static_cast<unsigned char const *>(in);

#ifdef MONAD_ZKVM_ZISK
    // ZisK executes an unaligned load directly (the MemAlign state machine),
    // so the sponge needs no alignment case at all: one loop, one load per
    // lane, whatever `in` is aligned to.
    //
    // load64 is one `ld` here because the guest is built -mtune=size;
    // under the default tuning it would be byte-staged and this loop would be
    // far worse than the branch it replaces. The two changes are coupled.
    //
    // Stage a misaligned multi-block input once, then absorb it aligned.
    //
    // 136 is a multiple of 8, so the whole sponge inherits the alignment of the
    // first byte: a misaligned `in` makes every one of the 17 lanes of every
    // block a boundary-crossing load at 159 against 16.
    alignas(8) unsigned char staged[8 * RATE];
    if ((reinterpret_cast<uintptr_t>(p) & 7) != 0 && len >= RATE &&
        len <= sizeof(staged)) {
        std::memcpy(staged, p, len);
        p = staged;
    }

    // The first block is a copy rather than a xor, into a rate nothing has
    // cleared -- and -mzisk-dma lowers that 136-byte copy to ZisK's block-move
    // precompile. `first` tracks whether anything has been absorbed yet.
    bool first = true;
    while (len >= RATE) {
        if (first) {
            std::memcpy(st, p, RATE);
            first = false;
        }
        else {
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= load64(p + 8 * i);
            }
        }
        if constexpr (Prefix) {
            if (memo_blocks != 0) {
                --memo_blocks;
                keccak_permute<true>(&st);
            }
            else {
                keccak_permute<false>(&st);
            }
        }
        else {
            keccak_permute<Memo>(&st);
        }
        p += RATE;
        len -= RATE;
    }
#else
    // SP1 is rv32im and its handling of unaligned access has not been
    // established, so it keeps the alignment split.
    uintptr_t const mis = reinterpret_cast<uintptr_t>(p) & 7;

    if (mis == 0) {
        while (len >= RATE) {
            auto const *const w = reinterpret_cast<uint64_t const *>(p);
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
            keccak_permute<Memo>(&st);
            p += RATE;
            len -= RATE;
        }
    }
    else {
        // Shift-combine over aligned reads. Each block consumes w[0..17]:
        // w[17]'s highest bytes sit past p+RATE, so the loop requires a full
        // block to FOLLOW (len > RATE + 7) and the last full block falls
        // through to the buffered path below rather than reading past the
        // caller's input.
        unsigned const rs = 8u * static_cast<unsigned>(mis);
        unsigned const ls = 64u - rs;
        while (len > RATE + 7) {
            auto const *const w = reinterpret_cast<uint64_t const *>(p - mis);
            uint64_t lo = w[0];
            for (size_t i = 0; i < WORDS; ++i) {
                uint64_t const hi = w[i + 1];
                st[i] ^= (lo >> rs) | (hi << ls);
                lo = hi;
            }
            keccak_permute<Memo>(&st);
            p += RATE;
            len -= RATE;
        }
        if (len >= RATE) { // the trailing full block, via the aligned buffer
            alignas(8) unsigned char blk[RATE];
            std::memcpy(blk, p, RATE);
            auto const *const w = reinterpret_cast<uint64_t const *>(blk);
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
            keccak_permute<Memo>(&st);
            p += RATE;
            len -= RATE;
        }
    }
#endif

    // Final block: remainder plus pad10*1 with the 0x01 domain byte.
    if (first) {
        // Nothing absorbed yet, so the padded block can be built in the state
        // itself: no 136-byte scratch to zero, no copy into it, and no 17-lane
        // xor to fold it in. This is the common shape -- a trie node, an
        // address, a slot -- everything under one rate block.
        if (len) {
            std::memcpy(st, p, len);
        }
        auto *const b = reinterpret_cast<unsigned char *>(st);
        b[len] = 0x01;
        // The high pad bit lands at byte RATE-1 = 135, which is byte 7 of lane
        // 16 -- a constant position, so the lane takes it whole. The byte store
        // is 193 cells against 34 for the aligned pair, and this runs once per
        // call. `len` is not constant and stays a byte store: a variable lane
        // index costs the shift it would save.
        static_assert(RATE - 1 == 16 * 8 + 7);
        st[16] |= uint64_t{0x80} << 56;
    }
    else {
        alignas(8) unsigned char last[RATE] = {};
        if (len) {
            std::memcpy(last, p, len);
        }
        last[len] = 0x01;
        auto const *const w = reinterpret_cast<uint64_t const *>(last);
        // Skip zero lanes beyond the domain byte. Each branch uses a constant
        // lane count to preserve loop unrolling; a runtime count measured
        // worse.
        if (len <= 31) {
            for (size_t i = 0; i < 4; ++i) {
                st[i] ^= w[i];
            }
        }
        else if (len <= 63) {
            for (size_t i = 0; i < 8; ++i) {
                st[i] ^= w[i];
            }
        }
        else if (len <= 95) {
            for (size_t i = 0; i < 12; ++i) {
                st[i] ^= w[i];
            }
        }
        else if (len <= 127) {
            for (size_t i = 0; i < 16; ++i) {
                st[i] ^= w[i];
            }
        }
        else {
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
        }
        // The high pad bit goes into the state, not into `last`, for the reason
        // the `first` arm above already gives: byte RATE-1 is byte 7 of lane 16,
        // a constant position, so the lane takes it whole. In `last` it is a
        // read-modify-write whose `|= 0x80` gcc lowers to `ori rd, rs, -128` --
        // a source register with bits 63..8 set, which prices the store at the
        // 193-cell dirty form rather than 66. Here it is an xor of a constant
        // into an aligned lane, and xor is commutative so the digest is
        // unchanged: `last[RATE-1]` contributes to nothing else.
        st[16] ^= uint64_t{0x80} << 56;
    }
    keccak_permute<Memo>(&st);

    std::memcpy(out, st, 32);
}

#ifdef MONAD_ZKVM_ZISK
// The constant-length entries monad_keccak256 picks when its length folds; see
// keccak256_one_block_n. The known-input table is asked first, as the general
// entry asks it, here with the length folded into its probe. With the memo
// compiled out a miss is the plain sponge at that length, so the header can
// name the entries without knowing whether the memo is in.
template <size_t N>
[[gnu::always_inline]] static inline void
keccak256_n(void const *in, uint8_t out[32])
{
    // Tied to their argument registers, as in monad_zkvm_keccak256_fast.
    asm("" : "+r"(in), "+r"(out));
    if (monad::zkvm::known_input_hash(
            static_cast<unsigned char const *>(in), N, out)) {
        return;
    }
    #if MONAD_ZKVM_KECCAKF_MEMO
    keccak256_one_block_n<N>(in, out);
    #else
    keccak256_sponge<true>(in, N, out);
    #endif
}
#endif

#if defined(MONAD_ZKVM_ZISK) && MONAD_ZKVM_KECCAKF_MEMO
template <Filing F>
static void keccak256_trie(void const *in, size_t len, uint8_t out[32])
{
    // Tied to their argument registers: gcc otherwise takes a0 and a1 for the
    // one-block arm's temporaries and moves the arguments out on every call,
    // the two thirds that only pass them on included.
    asm("" : "+r"(in), "+r"(len), "+r"(out));
    if (len < 136) {
        keccak256_one_block_fresh(in, len, out);
    }
    else if ((reinterpret_cast<uintptr_t>(in) & 7) == 0) {
        keccak256_memo_digest<MemoFrom::Aligned, F>(in, len, out);
    }
    else if (len <= MEMO_STAGED_BYTES) {
        keccak256_memo_digest<MemoFrom::Staged, F>(in, len, out);
    }
    else {
        keccak256_memo_digest<MemoFrom::Misaligned, F>(in, len, out);
    }
}

// keccak256_trie's sponge, at least a rate block, from a SpongeEntry and its
// argument.
template <Filing F, SpongeEntry Entry, typename Extra>
static void keccak256_trie_entry(
    void const *const in, size_t const len, uint8_t out[32], Extra const extra)
{
    if ((reinterpret_cast<uintptr_t>(in) & 7) == 0) {
        keccak256_memo_digest<MemoFrom::Aligned, F, Entry>(in, len, out, extra);
    }
    else if (len <= MEMO_STAGED_BYTES) {
        keccak256_memo_digest<MemoFrom::Staged, F, Entry>(in, len, out, extra);
    }
    else {
        keccak256_memo_digest<MemoFrom::Misaligned, F, Entry>(
            in, len, out, extra);
    }
}
#endif

extern "C"
{

void monad_zkvm_keccak256_fast(void const *in, size_t len, uint8_t out[32])
{
#if defined(MONAD_ZKVM_ZISK)
    // Tied to their argument registers: gcc otherwise takes a0 to a2 for the
    // table lookup's temporaries and moves the arguments out on every call.
    asm("" : "+r"(in), "+r"(len), "+r"(out));
#endif
    if (monad::zkvm::known_input_hash(
            static_cast<unsigned char const *>(in), len, out)) {
        return;
    }
    keccak256_sponge<true>(in, len, out);
}

#ifdef MONAD_ZKVM_ZISK
void monad_zkvm_keccak256_20(void const *const in, uint8_t out[32])
{
    keccak256_n<20>(in, out);
}

void monad_zkvm_keccak256_32(void const *const in, uint8_t out[32])
{
    keccak256_n<32>(in, out);
}

void monad_zkvm_keccak256_64(void const *const in, uint8_t out[32])
{
    keccak256_n<64>(in, out);
}
#endif

// A trie node's digest as the pre-state check takes it, and as the post-state
// takes it again (Filing). An input of one rate block is neither looked up nor
// filed: see keccak256_one_block_fresh.
#if defined(MONAD_ZKVM_ZISK) && MONAD_ZKVM_KECCAKF_MEMO
void monad_zkvm_keccak256_trie_prime(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_trie<Filing::NotFinal>(in, len, out);
}

void monad_zkvm_keccak256_trie_patch(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_trie<Filing::None>(in, len, out);
}

// A trie node primed with a rate block or more, whose RLP is later patched in
// place past its leading blocks: the patched digest starts from the state the
// priming hash left after them instead of asking for each of them again, a
// hint request and a 200-byte compare a block.
void monad_zkvm_keccak256_trie_prime_mark(
    void const *const in, size_t const len, uint8_t out[32],
    uint64_t *const mark)
{
    keccak256_trie_entry<Filing::NotFinal, SpongeEntry::Prime>(
        in, len, out, mark);
}

// SOUNDNESS. The mark is guest memory the prime wrote, not a hint, and the
// state it names is checked the way a hint's index is: below
// `keccakf_memo_used`, so inside the table this execution has written, whose
// entries never change once counted. The prime filed its whole blocks in
// consecutive slots from mark - 1, and a slot past the table's end is never
// below the count, so a slot that passes is the prime's own state after
// `blocks` blocks: the real permutations of those bytes, which the caller
// vouches are this input's first `blocks` blocks.
void monad_zkvm_keccak256_trie_resume(
    void const *const in, size_t const len, uint8_t out[32],
    uint64_t const mark, size_t const blocks)
{
    uint64_t const at = mark - 1 + blocks - 1;
    if (mark != 0 && at < hot->keccakf_memo_used) {
        size_t const skip = blocks * 136;
        keccak256_trie_entry<Filing::None, SpongeEntry::Resume>(
            static_cast<unsigned char const *>(in) + skip,
            len - skip,
            out,
            static_cast<uint64_t const *>(hot->keccakf_memo[at].out));
        return;
    }
    keccak256_trie<Filing::None>(in, len, out);
}
#else
void monad_zkvm_keccak256_trie_prime(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<true>(in, len, out);
}

void monad_zkvm_keccak256_trie_patch(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<true>(in, len, out);
}
#endif

// The same sponge with the Keccak-f memo compiled out of it, for inputs whose
// permutations are known in advance never to repeat.
//
// The memo pays 2 x 1,232 cells on every MISS -- keccakf_state_copy of the
// input state before the permutation and of the output after it -- against
// 38,454 saved on a hit, so it is a bet that a state recurs. Contract bytecode
// is the one input where the bet is certain to lose: the 395 bodies a block
// carry 28,451 of the 120,701 permutations and they are all distinct
// contents, so no state in a bytecode's chain has been seen before or will be
// seen again. Filing them is 82.5 M cells for zero hits, and it is also the
// only site large enough to be worth splitting: the rest of the block's rate
// blocks hit 12.1 %, above the 10.27 % break-even.
//
// The transactions and receipts trie leaves of a full rate block or more, and
// the signing payloads of that size, lose the same bet: a leaf or payload's
// first block carries a nonce and fees, or a receipt's cumulative gas, so its
// chain almost never starts from a state an earlier call filed. Shorter ones
// are one block and keep the memo's one-block shape.
//
// Soundness is unaffected in both directions. Not filing an entry can only
// cost a later hint; and a permutation that runs without a preceding
// `fcall_set_keccakf_index` leaves the executor's next filing under a stale
// index, which `keccakf_state_eq` rejects on the way out -- a poisoned entry,
// never a wrong digest. That is the same argument the memo already relies on
// for zisklib's own permutations, which run through this binary unannounced.
void monad_zkvm_keccak256_fast_nomemo(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<false>(in, len, out);
}

// The same sponge, with the memo on its first `memo_blocks` rate blocks only:
// for a bytecode whose chain recurs as far as the prefix it shares with
// another, and no further. The argument above covers both halves: the memo's
// two checks on the blocks it serves, and nothing filed on the others.
void monad_zkvm_keccak256_fast_memo_prefix(
    void const *const in, size_t len, size_t const memo_blocks,
    uint8_t out[32])
{
#if defined(MONAD_ZKVM_ZISK) && MONAD_ZKVM_KECCAKF_MEMO
    keccak256_sponge<false, true>(in, len, out, memo_blocks);
#else
    (void)memo_blocks;
    keccak256_sponge<false>(in, len, out);
#endif
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_SP1
