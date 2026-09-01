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
// After the pre-state binding the guest performs ~110 k permutations per
// block, so the wrapper alone was worth ~15 % of the guest. This entry
// absorbs word-wise: 17 ld+xor on an aligned block, shift-combine on a
// misaligned one (aligned reads only, never past the input), and the tail
// goes through ZisK's emulator-accelerated memcpy.
//
// The permutation itself, the padding rule (0x01 domain, 0x80 close — the
// Ethereum keccak, not SHA-3) and the 136-byte rate are identical to
// zisklib's; only the marshalling differs. Every hash this guest emits is
// cross-checked against canonical mainnet data (block hash, pre/post state
// roots, body roots), so a divergence here cannot pass unnoticed.

// SP1's wrapper has the same disease in a different coat: zkvm_keccak256 is
// tiny_keccak's sponge in software (only keccak-f reaches the KECCAK_PERMUTE
// precompile), absorbing byte by byte -- measured at 19.5 % of the SP1 guest's
// attributed work, because the pre-state binding hashes the whole witness trie.

#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_SP1)

#include <cstddef>
#include <cstdint>
#include <cstring>


extern "C"
{

#ifdef MONAD_ZKVM_ZISK
// ziskos's raw precompile entry (no_mangle, extern "C"), the same door
// zisklib's own wrapper uses.
void syscall_keccak_f(uint64_t (*state)[25]);

// Keccak-f memo. OFF gives the exact control arm: the mechanism is compiled
// out, not disabled, so an A/B measures the memo rather than a predicate.
#ifdef MONAD_ZKVM_KECCAKF_MEMO

// ── the permutation memo ─────────────────────────────────────────────────
//
// A permutation is 38,454 of ZisK cost against 15-60 for an ordinary op, and
// keccak is 24.4 % of this guest's COST -- both on ziskemu 1.2, which repriced
// the precompiles 43.8 % below 1.1 and left every other category to the cell.
// The 1.2 numbers halve the memo's takings and leave its case stronger, since
// the alternative it was measured against is a guest-side cost that 1.2 did
// not touch. About 14 % of the permutations a
// block runs repeat a state an earlier one already permuted: 12.1-16.7 %
// over the 25815000-25815199 corpus, which is the same 13.6-15.7 % a
// fingerprint census over our own call stream reported independently.
//
// What makes the memo pay is that the LOOKUP is not in the proof. The guest
// does not hash the state; it asks the executor, which keeps the same map
// natively (zisk-core `opc_fcall`, plus the assembly emulator's copy in
// zisk-lib-c, so the prover's EXECUTE phase knows it too). `fcall_param`,
// `fcall` and `fcall_get` all cost ZERO in `zisk_ops_costs.rs`. A guest-side
// fingerprint over the 25 words was measured at +9.09 % COST on 1.1, where a
// permutation was worth twice what it is now -- so the margin against
// fingerprinting has only widened. Avoiding it is the whole reason this is
// worth building.
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
//
// GATE. Both checks must be shown live, and breaking either must break the
// corpus roots: drop the `index <` guard, and separately make the compare
// always succeed. A memo that reproduces 200 roots with a check removed is a
// memo whose check was never doing anything.
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

static KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES];
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

#endif // MONAD_ZKVM_KECCAKF_MEMO

// The only Keccak-f this guest runs. With the memo on it IS the permutation,
// with an earlier identical one reused when the executor knows of one.
static inline void keccak_permute(uint64_t (*state)[25])
{
#ifdef MONAD_ZKVM_KECCAKF_MEMO
    uint64_t *const s = &(*state)[0];
    uint64_t const index = fcall_get_keccakf_index(s);

    // Cheap check first, so an out-of-range index — which is what
    // KECCAKF_INDEX_NOT_FOUND is — never reaches the compare.
    if (index < keccakf_memo_used &&
        keccakf_state_eq(keccakf_memo[index].in, s)) {
        keccakf_state_copy(s, keccakf_memo[index].out);
        return;
    }

    if (keccakf_memo_used == KECCAKF_MEMO_ENTRIES) {
        // Full: keep permuting, stop remembering. Filing more would mean
        // evicting, and an evicted slot only ever produces hints that fail
        // the compare above.
        syscall_keccak_f(state);
        return;
    }

    // Nothing may come between the request and the permutation: the executor
    // files whichever Keccak-f runs next, and this binary has a second one --
    // zisklib's own keccak256, 154 permutations a block on the ecrecover
    // path. A stray permutation in between would file the wrong state under
    // this index. The compare above would reject the resulting hint, so it is
    // a poisoned entry rather than a wrong digest, but keep these adjacent.
    KeccakfEntry &e = keccakf_memo[keccakf_memo_used];
    keccakf_state_copy(e.in, s);
    fcall_set_keccakf_index(keccakf_memo_used);
    syscall_keccak_f(state);
    keccakf_state_copy(e.out, s);
    // Published last: this is what puts the entry in range, so it must not
    // move until both halves are there.
    ++keccakf_memo_used;
#else
    syscall_keccak_f(state);
#endif
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

// The guest absorbs with the vendored ethash sponge, which permutes through
// monad_keccakf1600 (zkvm/category/crypto/keccakf1600.h) rather than through a
// rate loop of its own. Export the memoised permutation so that entry reaches
// it. This file carries no sponge: 16e29d462 already gave the guest a word-wise
// one, inlined, and two would be one too many.
void monad_keccakf1600_memo(uint64_t state[25])
{
    keccak_permute(reinterpret_cast<uint64_t(*)[25]>(state));
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_SP1
