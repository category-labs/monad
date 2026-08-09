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

#include <category/core/bit_primitives.hpp>

extern "C"
{

#ifdef MONAD_ZKVM_ZISK
// ziskos's raw precompile entry (no_mangle, extern "C"), the same door
// zisklib's own wrapper uses.
void syscall_keccak_f(uint64_t (*state)[25]);

static inline void keccak_permute(uint64_t (*state)[25])
{
    syscall_keccak_f(state);
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
    constexpr size_t RATE = 136;
    constexpr size_t WORDS = RATE / 8; // 17

    uint64_t st[25] = {};
    auto const *p = static_cast<unsigned char const *>(in);
    uintptr_t const mis = reinterpret_cast<uintptr_t>(p) & 7;

    if (mis == 0) {
        while (len >= RATE) {
            auto const *const w = reinterpret_cast<uint64_t const *>(p);
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
            keccak_permute(&st);
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
            keccak_permute(&st);
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
            keccak_permute(&st);
            p += RATE;
            len -= RATE;
        }
    }

    // Final block: remainder plus pad10*1 with the 0x01 domain byte.
    alignas(8) unsigned char last[RATE] = {};
    if (len) {
        std::memcpy(last, p, len);
    }
    last[len] = 0x01;
    last[RATE - 1] |= 0x80;
    auto const *const w = reinterpret_cast<uint64_t const *>(last);
    for (size_t i = 0; i < WORDS; ++i) {
        st[i] ^= w[i];
    }
    keccak_permute(&st);

#ifdef MONAD_ZKVM_SP1
    // out is a caller buffer of arbitrary alignment; st is 8-aligned. Inline
    // the fixed-size copy instead of paying the memcpy call ~30 k times per
    // block (the v6 histogram's keccak-tail entry).
    monad::bits::copy32_from_aligned(out, reinterpret_cast<unsigned char const *>(st));
#else
    std::memcpy(out, st, 32);
#endif
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_SP1
