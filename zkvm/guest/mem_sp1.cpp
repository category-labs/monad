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

// Word-wise mem* for the SP1 guest. Rust compiler_builtins supplies the ones
// the link would otherwise pick, and they price badly on this target: memcmp
// is byte-by-byte, and memcpy falls back to a byte loop whenever source and
// destination are not co-aligned. Fresh 3-block profile: memcpy 21.7 %,
// memcmp 6.3 %, memset 5.5 %, memmove 3.2 % of the guest\x27s attributed work —
// over a third of the instruction stream. ZisK does not have this problem
// because zisklib ships word-wise assembly mem*; these are their portable
// C++ equivalents, aligned loads only (the target faults on misaligned),
// cross-alignment handled by the same shift-combine the keccak absorb uses.
//
// ZisK is deliberately excluded: its zisklib versions are already word-wise.

#ifdef MONAD_ZKVM_SP1

#include <cstddef>
#include <cstdint>

namespace
{
    using word = uintptr_t; // 32-bit on SP1
    constexpr size_t W = sizeof(word);

    inline word load_word(unsigned char const *const p)
    {
        return *reinterpret_cast<word const *>(p);
    }
}

extern "C"
{

void *memcpy(void *const dst, void const *const src, size_t n)
{
    auto *d = static_cast<unsigned char *>(dst);
    auto const *s = static_cast<unsigned char const *>(src);
    // Align the DESTINATION: stores are the expensive half of a copy.
    while (n != 0 && (reinterpret_cast<uintptr_t>(d) & (W - 1)) != 0) {
        *d++ = *s++;
        --n;
    }
    uintptr_t const mis = reinterpret_cast<uintptr_t>(s) & (W - 1);
    if (mis == 0) {
        for (; n >= 4 * W; d += 4 * W, s += 4 * W, n -= 4 * W) {
            auto *dw = reinterpret_cast<word *>(d);
            auto const *sw = reinterpret_cast<word const *>(s);
            dw[0] = sw[0];
            dw[1] = sw[1];
            dw[2] = sw[2];
            dw[3] = sw[3];
        }
        for (; n >= W; d += W, s += W, n -= W) {
            *reinterpret_cast<word *>(d) = load_word(s);
        }
    }
    else if (n > 2 * W) {
        // Cross-aligned: aligned reads around the source, shift-combine.
        // The loop needs w[i+1], so it stops a word early; the tail below
        // finishes — it never reads past the caller\x27s buffer.
        unsigned const rs = 8u * static_cast<unsigned>(mis);
        unsigned const ls = 8u * static_cast<unsigned>(W) - rs;
        auto const *sw = reinterpret_cast<word const *>(s - mis);
        word lo = sw[0];
        while (n > W + (W - 1)) {
            word const hi = sw[1];
            *reinterpret_cast<word *>(d) = (lo >> rs) | (hi << ls);
            lo = hi;
            ++sw;
            d += W;
            s += W;
            n -= W;
        }
    }
    while (n != 0) {
        *d++ = *s++;
        --n;
    }
    return dst;
}

void *memset(void *const dst, int const c, size_t n)
{
    auto *d = static_cast<unsigned char *>(dst);
    auto const b = static_cast<unsigned char>(c);
    while (n != 0 && (reinterpret_cast<uintptr_t>(d) & (W - 1)) != 0) {
        *d++ = b;
        --n;
    }
    // Splat b into every byte lane, whatever sizeof(word) is: ~word(0)/0xff
    // is 0x0101...01 at the native width. (The host-side fuzz caught the
    // 32-bit-constant version of this line leaving the top lanes empty.)
    word const fill =
        static_cast<word>(b) * (~static_cast<word>(0) / 0xffu);
    for (; n >= 4 * W; d += 4 * W, n -= 4 * W) {
        auto *dw = reinterpret_cast<word *>(d);
        dw[0] = fill;
        dw[1] = fill;
        dw[2] = fill;
        dw[3] = fill;
    }
    for (; n >= W; d += W, n -= W) {
        *reinterpret_cast<word *>(d) = fill;
    }
    while (n != 0) {
        *d++ = b;
        --n;
    }
    return dst;
}

int memcmp(void const *const a, void const *const b, size_t n)
{
    auto const *x = static_cast<unsigned char const *>(a);
    auto const *y = static_cast<unsigned char const *>(b);
    // Co-aligned (the common case here: 32-byte hash compares): word
    // equality scan, byte-resolve inside the first differing word. The
    // result is the sign of the first differing BYTE, so the word compare
    // is only ever used as an equality screen — no byte-order games.
    if (((reinterpret_cast<uintptr_t>(x) ^ reinterpret_cast<uintptr_t>(y)) &
         (W - 1)) == 0) {
        while (n != 0 && (reinterpret_cast<uintptr_t>(x) & (W - 1)) != 0) {
            if (*x != *y) {
                return *x < *y ? -1 : 1;
            }
            ++x;
            ++y;
            --n;
        }
        for (; n >= W; x += W, y += W, n -= W) {
            if (load_word(x) != load_word(y)) {
                break;
            }
        }
    }
    while (n != 0) {
        if (*x != *y) {
            return *x < *y ? -1 : 1;
        }
        ++x;
        ++y;
        --n;
    }
    return 0;
}

void *memmove(void *const dst, void const *const src, size_t const n)
{
    auto *d = static_cast<unsigned char *>(dst);
    auto const *s = static_cast<unsigned char const *>(src);
    if (d == s || n == 0) {
        return dst;
    }
    if (d < s || d >= s + n) {
        return memcpy(dst, src, n);
    }
    // Overlapping with dst inside [src, src+n): copy backward, word-wise on
    // the co-aligned stretch.
    size_t m = n;
    d += m;
    s += m;
    while (m != 0 && (reinterpret_cast<uintptr_t>(d) & (W - 1)) != 0) {
        *--d = *--s;
        --m;
    }
    if (((reinterpret_cast<uintptr_t>(s)) & (W - 1)) == 0) {
        for (; m >= W; ) {
            d -= W;
            s -= W;
            m -= W;
            *reinterpret_cast<word *>(d) = load_word(s);
        }
    }
    while (m != 0) {
        *--d = *--s;
        --m;
    }
    return dst;
}

} // extern "C"

#endif // MONAD_ZKVM_SP1
