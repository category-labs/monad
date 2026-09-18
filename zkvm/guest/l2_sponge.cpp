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

// See l2_sponge.hpp for the mode and why the rate is what it is.

#include <zkvm/guest/l2_sponge.hpp>

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/core/poseidon2.hpp>

#include <cstddef>
#include <cstdint>
#include <string_view>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr std::string_view domain_name(L2Domain const d)
{
    switch (d) {
    case L2Domain::kdf:
        return "kdf";
    case L2Domain::stream:
        return "stream";
    case L2Domain::auth:
        return "auth";
    }
    return "";
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::size_t l2_pack_bytes(
    std::span<unsigned char const> const in, std::span<std::uint64_t> const out)
{
    std::size_t const n =
        (in.size() + L2_BYTES_PER_ELEM - 1) / L2_BYTES_PER_ELEM;
    MONAD_ASSERT(out.size() >= n);

    // Seven bytes an element, so a whole-word load reads one byte too many --
    // which is in bounds for every element but the last, since 7e + 8 <= size
    // holds while e + 1 < n. Worth the split: ZisK charges an unaligned
    // eight-byte read 106 where seven single-byte reads are 25 each, and each
    // of those carries a step and a shift as well.
    static_assert(
        L2_BYTES_PER_ELEM == 7, "the mask below spells seven bytes out");
    constexpr std::uint64_t SEVEN_BYTES = 0x00FFFFFFFFFFFFFFULL;
    std::size_t e = 0;
    for (; e + 1 < n; ++e) {
        out[e] =
            load_le_unsafe<std::uint64_t>(in.data() + e * L2_BYTES_PER_ELEM) &
            SEVEN_BYTES;
    }
    if (n != 0) {
        std::size_t const base = e * L2_BYTES_PER_ELEM;
        std::uint64_t v = 0;
        for (std::size_t b = 0; base + b < in.size(); ++b) {
            v |= static_cast<std::uint64_t>(in[base + b]) << (8u * b);
        }
        out[e] = v;
    }
    // Every element is below 2**56, so canonical without a test.
    return n;
}

L2Sponge::L2Sponge(
    L2Domain const domain, std::span<L2IoOp const> const io_pattern,
    std::span<unsigned char const, 32> const context,
    std::string_view const label)
    : pattern_{io_pattern}
{
    MONAD_ASSERT(!io_pattern.empty());

    // SAFE's initial state: the capacity carries a tag over the encoded I/O
    // pattern and the domain, and the rate starts empty. The tag is what stops
    // two uses -- or two transcripts whose lengths differ -- from sharing an
    // initial state, so the pattern is normative and not a debugging aid.
    //
    // One rate block holds it by construction: this guest's patterns are a
    // handful of ops and a short label, and the assert in put_u32 says so
    // rather than truncating in silence.
    unsigned char buf[L2_SPONGE_RATE * L2_BYTES_PER_ELEM] = {};
    std::size_t n = 0;

    auto const put_u32 = [&buf, &n](std::uint32_t w) {
        MONAD_ASSERT(n + 4 <= sizeof(buf));
        buf[n++] = static_cast<unsigned char>(w >> 24);
        buf[n++] = static_cast<unsigned char>(w >> 16);
        buf[n++] = static_cast<unsigned char>(w >> 8);
        buf[n++] = static_cast<unsigned char>(w);
    };

    // One word per call, high bit set for a squeeze, and consecutive calls of
    // the same kind merged -- so a length split across two calls encodes the
    // same way as the single call, which is what makes the transcript rather
    // than the call boundaries the thing being committed to.
    for (std::size_t i = 0; i < io_pattern.size();) {
        MONAD_ASSERT(io_pattern[i].len > 0);
        std::uint64_t len = io_pattern[i].len;
        std::size_t j = i + 1;
        for (; j < io_pattern.size() &&
               io_pattern[j].squeeze == io_pattern[i].squeeze;
             ++j) {
            MONAD_ASSERT(io_pattern[j].len > 0);
            len += io_pattern[j].len;
        }
        MONAD_ASSERT(len < (std::uint64_t{1} << 31));
        put_u32(
            static_cast<std::uint32_t>(len) |
            (io_pattern[i].squeeze ? 0x80000000u : 0u));
        i = j;
    }

    // The caller's label, then the domain. Frozen with the suite's protocol
    // version: a build that changes either produces tags nothing else
    // reproduces, which is the intent -- it is a different protocol.
    MONAD_ASSERT(!label.empty());
    for (char const c : label) {
        MONAD_ASSERT(n < sizeof(buf));
        buf[n++] = static_cast<unsigned char>(c);
    }
    for (char const c : domain_name(domain)) {
        MONAD_ASSERT(n < sizeof(buf));
        buf[n++] = static_cast<unsigned char>(c);
    }

    // The caller's application context, last. See the header for why it is in
    // the tag rather than the rate, and why it arrives pre-hashed.
    MONAD_ASSERT(n + context.size() <= sizeof(buf));
    for (unsigned char const c : context) {
        buf[n++] = c;
    }

    // Poseidon2 and not keccak: one permutation is 5,488 cells against a
    // Keccak-f's 75,575 in ZisK's cost model, and it keeps one hash function
    // across the whole L2 surface. (POSEIDON_COST and KECCAK_COST, zisk
    // v1.1.0-alpha -- the revision the Cargo.lock pins; earlier revisions
    // priced Poseidon2 differently, so the figure is worth re-reading against
    // whatever is actually pinned.)
    std::uint64_t seed[16] = {};
    l2_pack_bytes({buf, n}, {seed, L2_SPONGE_RATE});
    monad_poseidon2_16(seed);
    for (std::size_t i = 0; i < 4; ++i) {
        st_[L2_SPONGE_RATE + i] = seed[i];
    }
}

void L2Sponge::permute()
{
    monad_poseidon2_16(st_);
}

void L2Sponge::charge(bool const squeeze)
{
    MONAD_ASSERT(op_ < pattern_.size());
    MONAD_ASSERT(pattern_[op_].squeeze == squeeze);
    ++done_;
    MONAD_ASSERT(done_ <= pattern_[op_].len);
    if (done_ == pattern_[op_].len) {
        ++op_;
        done_ = 0;
    }
}

void L2Sponge::absorb_one(std::uint64_t const elem)
{
    MONAD_ASSERT(elem < GOLDILOCKS_P);
    // A direction change permutes even on a part-filled rate: otherwise the
    // lanes squeezed next would still hold what was just absorbed.
    if (squeezing_ || pos_ == L2_SPONGE_RATE) {
        permute();
        pos_ = 0;
        squeezing_ = false;
    }
    st_[pos_] = goldilocks_add(st_[pos_], elem);
    ++pos_;
}

std::uint64_t L2Sponge::squeeze_one()
{
    if (!squeezing_ || pos_ == L2_SPONGE_RATE) {
        permute();
        pos_ = 0;
        squeezing_ = true;
    }
    // Already reduced: the permutation's outputs are field elements, which is
    // what poseidon2_test.cpp asserts lane by lane.
    return st_[pos_++];
}

void L2Sponge::absorb(std::span<std::uint64_t const> const elems)
{
    for (std::uint64_t const e : elems) {
        charge(false);
        absorb_one(e);
    }
}

void L2Sponge::squeeze(std::span<std::uint64_t> const out)
{
    for (std::uint64_t &o : out) {
        charge(true);
        o = squeeze_one();
    }
}

void L2Sponge::finish() const
{
    MONAD_ASSERT(op_ == pattern_.size() && done_ == 0);
}

MONAD_NAMESPACE_END
