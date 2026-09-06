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

#include <cstddef>
#include <cstdint>
#include <cstring>

constexpr size_t KECCAK_RATE = 136;

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
//   1. the index must be below the local entry count `used`, i.e. inside
//      the table THIS execution has written. That also subsumes the
//      not-found sentinel, which is ~0 and so never in range;
//   2. the entry it points at must hold THIS state, compared word for word.
//
// Only then is its output used, and that output was produced by this same
// execution running the real permutation. Keccak-f is a function, so equal
// inputs have equal outputs: a bad hint costs a wasted compare and never a
// wrong answer. The count advances only after both halves of an entry
// are written; the global count is updated when the digest is complete.
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

// One entry past capacity. `keccakf_memo[keccakf_memo_used]` is the scratch a
// one-block digest builds its state in (keccak256_one_block below), and
// `keccakf_memo_used` reaches KECCAKF_MEMO_ENTRIES when the table fills, so the
// slot has to exist for the sponge to have somewhere to stand. It is never
// filed and never in range: 512 B of .bss for one fewer bounds branch on the
// hot path.
static KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES + 1];
static uint64_t keccakf_memo_used = 0;

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
// The parameter register is pinned rather than left to a plain "r": the
// transpiler reads `csrrs x0, csr, x0` as a nop instead of a parameter push,
// so a constraint the compiler may satisfy with x0 pushes nothing and the
// fcall silently sees no arguments. `_zicsr` is already in the guest's
// -march, which is what lets these assemble at all.
constexpr uint64_t KECCAKF_INDEX_NOT_FOUND = ~uint64_t{0};

// File the input state of the NEXT permutation under `index`.
// Keep the request and that permutation adjacent: another Keccak-f call
// would associate the index with the wrong state.
static inline void fcall_set_keccakf_index(uint64_t const index)
{
    register unsigned long a0 asm("a0") = static_cast<unsigned long>(index);
    asm volatile("csrs 0x8F0, %0\n\t" // one parameter, by value
                 "csrwi 0x8C0, 24" // FCALL_SET_KECCAKF_CACHE_INDEX_ID
                 :
                 : "r"(a0)
                 : "memory");
}

// The index `state` was filed under, or KECCAKF_INDEX_NOT_FOUND.
static inline uint64_t fcall_get_keccakf_index(uint64_t const *const state)
{
    register unsigned long a0 asm("a0") =
        reinterpret_cast<unsigned long>(state);
    uint64_t index;
    asm volatile("csrs 0x8F8, %[st]\n\t" // one parameter: 25 words at [st]
                 "csrwi 0x8C0, 25\n\t" // FCALL_GET_KECCAKF_CACHE_INDEX_ID
                 "csrr %[idx], 0xFFE" // fcall_get: the index
                 : [idx] "=&r"(index)
                 : [st] "r"(a0)
                 : "memory");
    return index;
}

// For inputs shorter than one rate block, build the padded pre-state in the
// memo's scratch slot. A miss copies only the rate to `out`; a hit reuses
// cached output. When full, permute the spare's `in` directly.
//
// SOUNDNESS. Both of the memo's checks are here, unchanged and in the same
// order, and neither trusts the executor: the hint must be below
// `keccakf_memo_used`, and the entry it names must hold this state word for
// word. The scratch is `keccakf_memo[keccakf_memo_used]`, which is not below
// `keccakf_memo_used`, so it can never be served as its own hint; and
// `keccakf_memo_used` still moves only after both halves of the entry are
// written, so an index that arrives early is still out of range. A hit leaves
// the scratch unpublished for reuse. Entries own the compared bytes;
// the caller's buffer is never used as a cache key.
//
// Scratch must be zero on entry. Fresh .bss reads zero under ZisK's
// memory AIR. Recording a miss advances to a fresh slot; a hit clears
// the 136-byte rate. When full, the table reuses its spare slot and
// clears all 200 bytes after the in-place permutation.
static void keccak256_one_block(
    void const *const in, size_t const len, uint8_t out[32])
{
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");

    // A local count avoids global reloads after the fcalls' and permutation's
    // asm memory clobbers.
    uint64_t const used = keccakf_memo_used;
    KeccakfEntry &e = keccakf_memo[used];
    uint64_t *const s = e.in;

    if (len) {
        std::memcpy(s, in, len);
    }
    reinterpret_cast<unsigned char *>(s)[len] = 0x01;
    s[16] |= uint64_t{0x80} << 56;

    uint64_t const index = fcall_get_keccakf_index(s);
    if (index < used && keccakf_state_eq(keccakf_memo[index].in, s)) {
        std::memcpy(out, keccakf_memo[index].out, 32);
        // Clear 17 lanes (136 bytes) used by input and padding.
        // No permutation ran here, so the other 64 bytes are still zero.
        std::memset(s, 0, KECCAK_RATE);
        return;
    }

    if (used == KECCAKF_MEMO_ENTRIES) {
        // Full table: permute the spare slot, then clear it for reuse.
        zisk_keccakf(&e.in);
        std::memcpy(out, s, 32);
        std::memset(s, 0, KECCAKF_STATE_BYTES);
        return;
    }

    // Preserve `in`; copy only the rate to `out` for the permutation.
    // Both capacities are zero: this is the first block and `out` is unused.
    std::memcpy(e.out, s, 17 * sizeof(uint64_t));
    fcall_set_keccakf_index(used);
    zisk_keccakf(&e.out);
    // Make the entry available only after both states are complete.
    keccakf_memo_used = used + 1;
    std::memcpy(out, e.out, 32);
}

// Permute pre = keccakf_memo[used].in without changing it.
// A hit needs a valid index and an identical full input state.
// Hits return an earlier output; misses return pre + KECCAKF_LANES.
// First copies only the rate into a fresh output: both capacities are zero.
// Other blocks and the reused spare need all 200 bytes.
// Lookup=false skips hints but still computes and caches the permutation.
// used is local to the caller, which writes it back after the digest.
template <bool First, bool Lookup = true>
static inline uint64_t const *
keccakf_memo_permute(uint64_t *const pre, uint64_t &used)
{
    if constexpr (Lookup) {
        uint64_t const index = fcall_get_keccakf_index(pre);
        if (index < used && keccakf_state_eq(keccakf_memo[index].in, pre)) {
            return keccakf_memo[index].out;
        }
    }
    uint64_t *const slot_out = pre + KECCAKF_LANES;
    auto *const post = reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(slot_out);
    if (used == KECCAKF_MEMO_ENTRIES) {
        // The reused spare may hold an earlier output; overwrite all lanes.
        keccakf_state_copy(slot_out, pre);
        zisk_keccakf(post);
        return slot_out;
    }
    if constexpr (First) {
        std::memcpy(slot_out, pre, 17 * sizeof(uint64_t));
    }
    else {
        keccakf_state_copy(slot_out, pre);
    }
    // The executor associates this index with the next permutation.
    fcall_set_keccakf_index(used);
    zisk_keccakf(post);
    // Publish only after both input and output are complete.
    ++used;
    return slot_out;
}

// For inputs >= 136 bytes, build each pre-state in the memo's scratch slot
// and read the previous output in place, carrying its 64 capacity bytes.
// The scratch must be zero on entry for the first block's capacity.
// Later blocks overwrite all 25 lanes. On return, clear the scratch if a
// hit or full table left it in use; a published miss advances to a zero slot.
static void keccak256_memo_sponge(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    auto const *p = static_cast<unsigned char const *>(in);
    // Keep the count local across permutations; write it back once on return.
    uint64_t used = keccakf_memo_used;

    // Stage unaligned inputs that fit here to avoid repeated costly
    // unaligned 64-bit loads.
    alignas(8) unsigned char staged[8 * KECCAK_RATE];
    if ((reinterpret_cast<uintptr_t>(p) & 7) != 0 && len <= sizeof(staged)) {
        std::memcpy(staged, p, len);
        p = staged;
    }

    uint64_t *pre = keccakf_memo[used].in;
    std::memcpy(pre, p, KECCAK_RATE);
    p += KECCAK_RATE;
    len -= KECCAK_RATE;
    uint64_t const *post = keccakf_memo_permute<true>(pre, used);

    // Stop lookups after the first miss. This may forgo later hits, but
    // skipped lookups run the real permutation and cache it when space permits.
    bool look = post != pre + KECCAKF_LANES;
    while (look && len >= KECCAK_RATE) {
        pre = keccakf_memo[used].in;
        // Keep one opaque base pointer for the lanes to avoid extra saved
        // registers for their addresses.
        asm("" : "+r"(pre));
        for (size_t i = 0; i < WORDS; ++i) {
            pre[i] = post[i] ^ load64(p + 8 * i);
        }
        std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        post = keccakf_memo_permute<false>(pre, used);
        look = post != pre + KECCAKF_LANES;
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }
    while (len >= KECCAK_RATE) {
        pre = keccakf_memo[used].in;
        asm("" : "+r"(pre));
        for (size_t i = 0; i < WORDS; ++i) {
            pre[i] = post[i] ^ load64(p + 8 * i);
        }
        std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        post = keccakf_memo_permute<false, false>(pre, used);
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }

    // Absorb the remaining bytes and Keccak padding (0x01 ... 0x80).
    // The partial lane is read backwards from the input end; the preceding
    // full block keeps the eight-byte load within the input.
    pre = keccakf_memo[used].in;
    size_t const whole = len / 8;
    unsigned const rem = static_cast<unsigned>(len % 8);
    // Jump to the matching unrolled sequence with an aligned pointer load.
    // GCC's switch table needs an offset load, base addition and bounds check.
    // Here whole is in [0, 16] because len < KECCAK_RATE.
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
        lane |= load64(p + len - 8) >> (8 * (8 - rem));
    }
    pre[whole] = post[whole] ^ lane;
    std::memcpy(
        pre + whole + 1, post + whole + 1, (KECCAKF_LANES - 1 - whole) * 8);
    pre[16] ^= uint64_t{0x80} << 56;
    post = look ? keccakf_memo_permute<false>(pre, used)
                : keccakf_memo_permute<false, false>(pre, used);
    std::memcpy(out, post, 32);

    if (pre == keccakf_memo[used].in) {
        std::memset(pre, 0, KECCAKF_STATE_BYTES);
    }
    keccakf_memo_used = used;
}

#endif // MONAD_ZKVM_KECCAKF_MEMO

// Only `syscall_keccak_f` above and the two entry points below carry C linkage;
// everything between them is C++ and the sponge is a template, which may not have it.

// Raw permutation for the sponge's non-memo path.
static inline void keccak_permute(uint64_t (*state)[25])
{
    zisk_keccakf(state);
}
#else
// SP1's syscall_keccak_permute symbol is LTO-internalised inside libzkevm.a,
// so emit the ecall the SDK itself emits: t0 = KECCAK_PERMUTE (0x00_01_01_09),
// a0 = state, a1 = 0. The precompile rewrites the 25 u64 lanes in place.
static inline void keccak_permute(uint64_t (*state)[25])
{
    register uintptr_t a0 asm("a0") = reinterpret_cast<uintptr_t>(state);
    register uintptr_t a1 asm("a1") = 0;
    register uint32_t t0 asm("t0") = 0x00010109u;
    asm volatile("ecall" : "+r"(a0) : "r"(t0), "r"(a1) : "memory");
}
#endif

template <bool Memo>
static void keccak256_sponge(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17

#if defined(MONAD_ZKVM_ZISK) && MONAD_ZKVM_KECCAKF_MEMO
    // 69.8 % of this entry's calls are one rate block (33,123 of 47,455 on
    // 25815042 -- a key, an address, a leaf or extension node's RLP). They
    // have a cheaper shape than the general sponge; see keccak256_one_block.
    if constexpr (Memo) {
        if (len < KECCAK_RATE) {
            keccak256_one_block(in, len, out);
        }
        else {
            keccak256_memo_sponge(in, len, out);
        }
        return;
    }
#endif

#ifdef MONAD_ZKVM_ZISK
    // 200 bytes: rate in st[0..16], capacity in st[17..24].
    uint64_t st[25];
    // Skip 17 words (136 bytes) and zero only the 64-byte capacity.
    std::memset(st + WORDS, 0, sizeof(st) - KECCAK_RATE);
    if (len < KECCAK_RATE) {
        // Short inputs leave bytes untouched; zero the rate before padding.
        std::memset(st, 0, KECCAK_RATE);
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
    // Copy the first block into the rate; XOR subsequent blocks.
    // -mzisk-dma lowers the copy to ZisK's block-move precompile.
    bool first = true;
    while (len >= KECCAK_RATE) {
        if (first) {
            // Initialize all 136 rate bytes before the first permutation.
            std::memcpy(st, p, KECCAK_RATE);
            first = false;
        }
        else {
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= load64(p + 8 * i);
            }
        }
        keccak_permute(&st);
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }
#else
    // SP1 is rv32im and its handling of unaligned access has not been
    // established, so it keeps the alignment split.
    uintptr_t const mis = reinterpret_cast<uintptr_t>(p) & 7;

    if (mis == 0) {
        while (len >= KECCAK_RATE) {
            auto const *const w = reinterpret_cast<uint64_t const *>(p);
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
            keccak_permute(&st);
            p += KECCAK_RATE;
            len -= KECCAK_RATE;
        }
    }
    else {
        // Shift-combine over aligned reads. Each block consumes w[0..17]:
        // w[17] reaches past p+KECCAK_RATE, so require len > KECCAK_RATE + 7.
        // The last full block uses the buffered path below to stay in bounds.
        unsigned const rs = 8u * static_cast<unsigned>(mis);
        unsigned const ls = 64u - rs;
        while (len > KECCAK_RATE + 7) {
            auto const *const w = reinterpret_cast<uint64_t const *>(p - mis);
            uint64_t lo = w[0];
            for (size_t i = 0; i < WORDS; ++i) {
                uint64_t const hi = w[i + 1];
                st[i] ^= (lo >> rs) | (hi << ls);
                lo = hi;
            }
            keccak_permute(&st);
            p += KECCAK_RATE;
            len -= KECCAK_RATE;
        }
        if (len >= KECCAK_RATE) { // the trailing full block, via the aligned buffer
            alignas(8) unsigned char blk[KECCAK_RATE];
            std::memcpy(blk, p, KECCAK_RATE);
            auto const *const w = reinterpret_cast<uint64_t const *>(blk);
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
            keccak_permute(&st);
            p += KECCAK_RATE;
            len -= KECCAK_RATE;
        }
    }
#endif

    // Final block: remainder plus pad10*1 with the 0x01 domain byte.
    #ifdef MONAD_ZKVM_ZISK
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
        // The high pad bit lands at KECCAK_RATE-1 = 135, byte 7 of lane 16
        // -- a constant position, so the lane takes it whole. The byte store
        // is 193 cells against 34 for the aligned pair, and this runs once per
        // call. `len` is not constant and stays a byte store: a variable lane
        // index costs the shift it would save.
        static_assert(KECCAK_RATE - 1 == 16 * 8 + 7);
        st[16] |= uint64_t{0x80} << 56;
    }
    else
    #endif
    {
        alignas(8) unsigned char last[KECCAK_RATE] = {};
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
        // the `first` arm above already gives: byte 135 is byte 7 of lane 16,
        // a constant position, so the lane takes it whole. In `last` it is a
        // read-modify-write whose `|= 0x80` gcc lowers to `ori rd, rs, -128` --
        // a source register with bits 63..8 set, which prices the store at the
        // 193-cell dirty form rather than 66. Here it is an xor of a constant
        // into an aligned lane, and xor is commutative so the digest is
        // unchanged: `last[KECCAK_RATE-1]` contributes to nothing else.
        st[16] ^= uint64_t{0x80} << 56;
    }
    keccak_permute(&st);

    std::memcpy(out, st, 32);
}

extern "C"
{

void monad_zkvm_keccak256_fast(void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<true>(in, len, out);
}

// Skip memo lookups and bookkeeping for bytecode, whose permutation states
// rarely repeat. Not registering them only forgoes future cache hits;
// any hints for later calls still undergo the full input-state check.
void monad_zkvm_keccak256_fast_nomemo(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<false>(in, len, out);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_SP1
