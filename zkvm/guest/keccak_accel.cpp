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

extern "C"
{

#ifdef MONAD_ZKVM_ZISK
// ziskos's raw precompile entry (no_mangle, extern "C"), the same door
// zisklib's own wrapper uses.
void syscall_keccak_f(uint64_t (*state)[25]);

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

void monad_zkvm_keccak256_fast(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17

    uint64_t st[25] = {};
    auto const *p = static_cast<unsigned char const *>(in);

#ifdef MONAD_ZKVM_ZISK
    // ZisK executes an unaligned load directly (the MemAlign state machine),
    // so the sponge needs no alignment case at all: one loop, one load per
    // lane, whatever `in` is aligned to.
    //
    // load64 is one `ld` here because the guest is built -mtune=size;
    // under the default tuning it would be byte-staged and this loop would be
    // far worse than the branch it replaces.
    while (len >= KECCAK_RATE) {
        for (size_t i = 0; i < WORDS; ++i) {
            st[i] ^= load64(p + 8 * i);
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
    alignas(8) unsigned char last[KECCAK_RATE] = {};
    if (len) {
        std::memcpy(last, p, len);
    }
    last[len] = 0x01;
    last[KECCAK_RATE - 1] |= 0x80;
    auto const *const w = reinterpret_cast<uint64_t const *>(last);
    for (size_t i = 0; i < WORDS; ++i) {
        st[i] ^= w[i];
    }
    keccak_permute(&st);

    std::memcpy(out, st, 32);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_SP1
