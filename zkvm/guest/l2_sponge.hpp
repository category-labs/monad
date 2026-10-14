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

// SAFE sponge over Poseidon2-16 (eprint 2023/520): rate 12, capacity 4. Use
// ZisK's exact permutation, pinned by poseidon2_test_vectors(). Four
// Goldilocks capacity lanes give a generic threshold near 2**128.
//
// The caller must supply a suite/version label for domain separation. Width
// is fixed to the precompile; suites using another permutation need their own
// sponge.
//
// Absorption adds canonical field elements into the rate. Unlike the byte
// sponge monad_poseidon2_256, it needs no reduction-flags lane; callers must
// supply elements below p.

#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <string_view>

MONAD_NAMESPACE_BEGIN

/// The separated uses of the sponge. A distinct domain per use is what lets the
/// argument treat them as independent oracles; two uses sharing one would let a
/// mask be read off a tag, or the reverse.
enum class L2Domain : std::uint8_t
{
    kdf = 0,
    stream = 1,
    auth = 2,
};

/// One call in a SAFE I/O pattern.
struct L2IoOp
{
    bool squeeze;
    std::uint32_t len;
};

/// Lanes carrying data. The other four are the capacity.
inline constexpr std::size_t L2_SPONGE_RATE = 12;

/// Bytes packed into one field element. Seven and never eight: eight arbitrary
/// bytes can exceed the modulus, and the Poseidon AIR makes a lane at or above
/// it unprovable.
inline constexpr std::size_t L2_BYTES_PER_ELEM = 7;

/// Cache SAFE capacity tags by domain and merged I/O pattern. Context or
/// label changes clear the cache. Label identity is compared by address, so
/// label bytes must remain immutable while cached. Bounded round-robin
/// replacement; single-owner and not thread-safe.
class L2SpongeTags
{
public:
    L2SpongeTags() = default;

private:
    friend class L2Sponge;

    /// A pattern merging to more words than this bypasses the cache. The
    /// cipher's patterns merge to two.
    static constexpr std::size_t MAX_WORDS = 4;
    static constexpr std::size_t ENTRIES = 8;

    struct Entry
    {
        L2Domain domain;
        std::uint8_t words;
        std::uint32_t word[MAX_WORDS];
        std::uint64_t capacity[4];
    };

    /// Fills `capacity` with the tag for these inputs: from an entry when one
    /// matches, and otherwise computed and filed.
    void
    tag(L2Domain domain, std::span<std::uint32_t const> words,
        std::span<unsigned char const, 32> context, std::string_view label,
        std::uint64_t (&capacity)[4]);

    std::uint64_t context_[4]{};
    char const *label_{nullptr};
    std::size_t label_size_{0};
    std::size_t count_{0};
    std::size_t next_{0};
    Entry entries_[ENTRIES]{};
};

class L2Sponge
{
public:
    /// Enforce each declared absorb/squeeze length; finish() requires exact
    /// consumption. io_pattern must outlive the sponge.
    ///
    /// The tag hashes the pattern, required suite/version label, domain and
    /// 32-byte context digest. Prehashing block constants avoids repeatedly
    /// absorbing them per transaction.
    ///
    /// All tag inputs must fit 84 bytes. Current patterns/domains take 14 and
    /// context takes 32, leaving 38 for the label. Oversize input asserts at
    /// runtime rather than truncating.
    L2Sponge(
        L2Domain domain, std::span<L2IoOp const> io_pattern,
        std::span<unsigned char const, 32> context, std::string_view label);

    /// The same sponge, opened on a tag from `tags` when that cache has seen
    /// this domain, merged pattern, context and label, and on one computed and
    /// filed there otherwise. What it produces is identical either way.
    L2Sponge(
        L2Domain domain, std::span<L2IoOp const> io_pattern,
        std::span<unsigned char const, 32> context, std::string_view label,
        L2SpongeTags &tags);

    /// Every element must be canonical (< GOLDILOCKS_P). The callers that pack
    /// bytes get that for free; the ones absorbing integers are bounded.
    void absorb(std::span<std::uint64_t const> elems);

    void squeeze(std::span<std::uint64_t> out);

    /// Asserts the declared pattern was consumed exactly. Not a destructor:
    /// an unmet pattern is a programming error, and halting from a destructor
    /// would hide which sponge was wrong.
    void finish() const;

private:
    L2Sponge(
        L2Domain domain, std::span<L2IoOp const> io_pattern,
        std::span<unsigned char const, 32> context, std::string_view label,
        L2SpongeTags *tags);

    void permute();
    /// Consumes `n` elements of the declared pattern, asserting that each op
    /// they reach is of kind `squeeze` and that they do not overrun it.
    void charge(bool squeeze, std::size_t n);

    std::uint64_t st_[16]{};
    std::size_t pos_{0};
    bool squeezing_{false};
    /// No permutation yet: the rate still holds the zeros it was built with.
    bool fresh_{true};
    std::span<L2IoOp const> pattern_;
    std::size_t op_{0};
    std::uint32_t done_{0};
};

/// Pack seven bytes per element, little-endian, zero-padding the last. Return
/// ceil(len/7), which must fit out. Callers must authenticate the exact byte
/// length to distinguish padded encodings.
std::size_t
l2_pack_bytes(std::span<unsigned char const> in, std::span<std::uint64_t> out);

MONAD_NAMESPACE_END
