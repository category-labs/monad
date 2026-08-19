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

// keccak256 for the ZisK guest, entered directly at the precompile.
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

#ifdef MONAD_ZKVM_ZISK

#include <cstddef>
#include <cstdint>
#include <cstring>

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

// ziskos's raw precompile entry (no_mangle, extern "C"), the same door
// zisklib's own wrapper uses.
void syscall_keccak_f(uint64_t (*state)[25]);

static inline void keccak_permute(uint64_t (*state)[25])
{
    syscall_keccak_f(state);
}

void monad_zkvm_keccak256_fast(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t RATE = 136;
    constexpr size_t WORDS = RATE / 8; // 17

    uint64_t st[25] = {};
    auto const *p = static_cast<unsigned char const *>(in);

#ifdef MONAD_ZKVM_ZISK
    // ZisK executes an unaligned load directly (the MemAlign state machine),
    // so the sponge needs no alignment case at all: one loop, one load per
    // lane, whatever `in` is aligned to.
    //
    // load64 is one `ld` here because the guest is built -mtune=generic-ooo;
    // under the default tuning it would be byte-staged and this loop would be
    // far worse than the branch it replaces.
    while (len >= RATE) {
        for (size_t i = 0; i < WORDS; ++i) {
            st[i] ^= load64(p + 8 * i);
        }
        keccak_permute(&st);
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
#endif

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

    std::memcpy(out, st, 32);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK
