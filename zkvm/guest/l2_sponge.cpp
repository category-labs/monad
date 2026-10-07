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

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
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

// The tag block is one rate block, 84 bytes, so at most 21 pattern words fit
// in it -- and fewer once the label and the context are in.
constexpr std::size_t MAX_PATTERN_WORDS =
    L2_SPONGE_RATE * L2_BYTES_PER_ELEM / 4;

// Encode SAFE operations as words (high bit = squeeze), merging adjacent
// operations of the same kind so call splitting does not change the tag.
// Return the word count.
std::size_t merge_pattern(
    std::span<L2IoOp const> const io_pattern,
    std::uint32_t (&words)[MAX_PATTERN_WORDS])
{
    std::size_t count = 0;
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
        MONAD_ASSERT(count < MAX_PATTERN_WORDS);
        words[count++] = static_cast<std::uint32_t>(len) |
                         (io_pattern[i].squeeze ? 0x80000000u : 0u);
        i = j;
    }
    return count;
}

// SAFE initializes capacity from the I/O pattern, label, domain and context;
// rate starts zero. These four inputs also define the cache key.
void safe_tag(
    L2Domain const domain, std::span<std::uint32_t const> const words,
    std::span<unsigned char const, 32> const context,
    std::string_view const label, std::uint64_t (&capacity)[4])
{
    // Bounds keep the tag input within one rate block. No zero fill is
    // needed: l2_pack_bytes reads only the n initialized bytes, including
    // word loads.
    unsigned char buf[L2_SPONGE_RATE * L2_BYTES_PER_ELEM];
    std::size_t n = 0;
    for (std::uint32_t const w : words) {
        buf[n++] = static_cast<unsigned char>(w >> 24);
        buf[n++] = static_cast<unsigned char>(w >> 16);
        buf[n++] = static_cast<unsigned char>(w >> 8);
        buf[n++] = static_cast<unsigned char>(w);
    }

    // Append the versioned suite label, domain and context digest under one
    // combined bound. Changing a label/domain changes the protocol tags.
    std::string_view const name = domain_name(domain);
    MONAD_ASSERT(
        n + label.size() + name.size() + context.size() <= sizeof(buf));
    std::memcpy(buf + n, label.data(), label.size());
    n += label.size();
    std::memcpy(buf + n, name.data(), name.size());
    n += name.size();
    std::memcpy(buf + n, context.data(), context.size());
    n += context.size();

    // Use Poseidon2 for lower proving cost. Consult the pinned ZisK cost
    // table for POSEIDON_COST and KECCAK_COST; both vary by revision.
    std::uint64_t seed[16] = {};
    l2_pack_bytes({buf, n}, {seed, L2_SPONGE_RATE});
    monad_poseidon2_16(seed);
    for (std::size_t i = 0; i < 4; ++i) {
        capacity[i] = seed[i];
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::size_t l2_pack_bytes(
    std::span<unsigned char const> const in, std::span<std::uint64_t> const out)
{
    std::size_t const n =
        (in.size() + L2_BYTES_PER_ELEM - 1) / L2_BYTES_PER_ELEM;
    MONAD_ASSERT(out.size() >= n);

    // Word loads are in bounds while e+1 < n because 7e+8 <= size. Mask the
    // extra byte; load the final element bytewise.
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

void L2SpongeTags::tag(
    L2Domain const domain, std::span<std::uint32_t const> const words,
    std::span<unsigned char const, 32> const context,
    std::string_view const label, std::uint64_t (&capacity)[4])
{
    MONAD_ASSERT(words.size() <= MAX_WORDS);
    std::uint64_t ctx[4];
    for (std::size_t i = 0; i < 4; ++i) {
        ctx[i] = load_le_unsafe<std::uint64_t>(context.data() + 8 * i);
    }
    // Bound to one context and one label: a sponge over any other empties the
    // cache first, so no tag outlives the inputs it was computed from.
    if (label.data() != label_ || label.size() != label_size_ ||
        ctx[0] != context_[0] || ctx[1] != context_[1] ||
        ctx[2] != context_[2] || ctx[3] != context_[3]) {
        for (std::size_t i = 0; i < 4; ++i) {
            context_[i] = ctx[i];
        }
        label_ = label.data();
        label_size_ = label.size();
        count_ = 0;
        next_ = 0;
    }
    for (std::size_t e = 0; e < count_; ++e) {
        Entry const &x = entries_[e];
        if (x.domain == domain && x.words == words.size() &&
            std::equal(words.begin(), words.end(), x.word)) {
            for (std::size_t i = 0; i < 4; ++i) {
                capacity[i] = x.capacity[i];
            }
            return;
        }
    }
    safe_tag(domain, words, context, label, capacity);
    Entry &x = entries_[next_];
    x.domain = domain;
    x.words = static_cast<std::uint8_t>(words.size());
    std::copy(words.begin(), words.end(), x.word);
    for (std::size_t i = 0; i < 4; ++i) {
        x.capacity[i] = capacity[i];
    }
    next_ = (next_ + 1) % ENTRIES;
    if (count_ < ENTRIES) {
        ++count_;
    }
}

L2Sponge::L2Sponge(
    L2Domain const domain, std::span<L2IoOp const> const io_pattern,
    std::span<unsigned char const, 32> const context,
    std::string_view const label)
    : L2Sponge{domain, io_pattern, context, label, nullptr}
{
}

L2Sponge::L2Sponge(
    L2Domain const domain, std::span<L2IoOp const> const io_pattern,
    std::span<unsigned char const, 32> const context,
    std::string_view const label, L2SpongeTags &tags)
    : L2Sponge{domain, io_pattern, context, label, &tags}
{
}

L2Sponge::L2Sponge(
    L2Domain const domain, std::span<L2IoOp const> const io_pattern,
    std::span<unsigned char const, 32> const context,
    std::string_view const label, L2SpongeTags *const tags)
    : pattern_{io_pattern}
{
    MONAD_ASSERT(!io_pattern.empty());
    MONAD_ASSERT(!label.empty());
    std::uint32_t words[MAX_PATTERN_WORDS];
    std::size_t const count = merge_pattern(io_pattern, words);
    std::uint64_t capacity[4];
    if (tags != nullptr && count <= L2SpongeTags::MAX_WORDS) {
        tags->tag(domain, {words, count}, context, label, capacity);
    }
    else {
        safe_tag(domain, {words, count}, context, label, capacity);
    }
    for (std::size_t i = 0; i < 4; ++i) {
        st_[L2_SPONGE_RATE + i] = capacity[i];
    }
}

void L2Sponge::permute()
{
    monad_poseidon2_16(st_);
    fresh_ = false;
}

void L2Sponge::charge(bool const squeeze, std::size_t n)
{
    // The same acceptance as charging one element at a time: every op the
    // call reaches must be of its kind, and the call may not run past the
    // pattern -- it only stops at op boundaries rather than at each element.
    while (n > 0) {
        MONAD_ASSERT(op_ < pattern_.size());
        L2IoOp const &op = pattern_[op_];
        MONAD_ASSERT(op.squeeze == squeeze);
        std::uint32_t const left = op.len - done_;
        std::uint32_t const take =
            n < left ? static_cast<std::uint32_t>(n) : left;
        done_ += take;
        n -= take;
        if (done_ == op.len) {
            ++op_;
            done_ = 0;
        }
    }
}

void L2Sponge::absorb(std::span<std::uint64_t const> const elems)
{
    charge(false, elems.size());
    std::size_t pos = pos_;
    for (std::size_t i = 0; i < elems.size();) {
        // A direction change permutes even on a part-filled rate: otherwise
        // the lanes squeezed next would still hold what was just absorbed.
        if (squeezing_ || pos == L2_SPONGE_RATE) {
            permute();
            pos = 0;
            squeezing_ = false;
        }
        std::size_t const room = L2_SPONGE_RATE - pos;
        std::size_t const end =
            elems.size() - i < room ? elems.size() : i + room;
        if (fresh_) {
            // Until the first permutation the rate is the zero it was built
            // with, and each lane is written once before that permutation --
            // so adding into it is adding to zero, which is the element.
            for (; i < end; ++i) {
                MONAD_ASSERT(elems[i] < GOLDILOCKS_P);
                st_[pos++] = elems[i];
            }
        }
        else {
            for (; i < end; ++i) {
                MONAD_ASSERT(elems[i] < GOLDILOCKS_P);
                st_[pos] = goldilocks_add(st_[pos], elems[i]);
                ++pos;
            }
        }
        pos_ = pos;
    }
}

void L2Sponge::squeeze(std::span<std::uint64_t> const out)
{
    charge(true, out.size());
    std::size_t pos = pos_;
    for (std::size_t i = 0; i < out.size();) {
        if (!squeezing_ || pos == L2_SPONGE_RATE) {
            permute();
            pos = 0;
            squeezing_ = true;
        }
        std::size_t const room = L2_SPONGE_RATE - pos;
        std::size_t const end = out.size() - i < room ? out.size() : i + room;
        // Already reduced: the permutation's outputs are field elements,
        // which is what poseidon2_test.cpp asserts lane by lane.
        for (; i < end; ++i) {
            out[i] = st_[pos++];
        }
        pos_ = pos;
    }
}

void L2Sponge::finish() const
{
    MONAD_ASSERT(op_ == pattern_.size() && done_ == 0);
}

MONAD_NAMESPACE_END
