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

// A SAFE sponge over Poseidon2-16 (eprint 2023/520), for the L2's encrypted
// transactions: rate 12 (lanes 0-11), capacity 4 (lanes 12-15).
//
// It carries no protocol identity of its own. The `label` a caller passes is
// hashed into every tag, so two cipher suites (l2_cipher_suite.hpp) can share
// this machinery and still be separated oracles without either having to know
// the other exists. There is deliberately no default label: a default is how
// two suites would come to share one by omission, and the separation would
// then rest on their contexts happening to differ.
//
// Not templated on the width, deliberately. A second width means a second
// Poseidon2 instance, and any instance but the precompile's runs in software at
// roughly an order of magnitude more -- so it is not a production alternative,
// and parameterising for it would be generality bought at the price of
// touching a working sponge. A suite wanting another permutation writes its
// own; this one is reusable as it stands.
//
// Width 16 is the permutation ZisK's precompile implements, and is therefore
// the instance this protocol version freezes -- constants, matrices and rounds
// are whatever category/core/poseidon2.cpp reproduces and
// poseidon2_test_vectors() pins, not a transcription of some other Goldilocks
// instance. The width does not dictate the capacity: reserving four lanes and
// absorbing on the other twelve is this mode's choice, and four Goldilocks
// lanes is just under 256 bits, so the generic sponge threshold is about
// 2**128.
//
// Absorption ADDS into the rate, where monad_poseidon2_256 overwrites. The
// difference is not stylistic: that sponge absorbs arbitrary bytes, so eight of
// them are not always a canonical field element and it has to carry a lane of
// "was reduced" flags to keep the map injective. Everything absorbed here is
// either a seven-byte-packed element or a bounded integer, hence below 2**56
// and canonical by construction -- so there is no flags lane, and the full
// twelve-lane rate is available.

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

class L2Sponge
{
public:
    /// `io_pattern` is hashed into the initial capacity and then enforced: each
    /// absorb and squeeze must match the declared op and length, and finish()
    /// requires the pattern to have been consumed exactly. The span must
    /// outlive the sponge -- callers pass a static or stack array.
    ///
    /// `context` is 32 bytes of application context, hashed into the tag
    /// alongside the pattern and the domain. SAFE's domain separator is where
    /// application binding belongs, and putting the caller's block-constant
    /// fields there rather than in the rate is what keeps them off the
    /// per-transaction path: they bind just as tightly -- they determine the
    /// tag, and the tag determines every lane the sponge ever produces -- while
    /// costing one hash a block instead of an absorption per transaction per
    /// domain.
    ///
    /// It is a DIGEST and not the fields themselves because the tag input is
    /// one rate block: the pattern words, the label and the domain already fill
    /// part of it, and the fields would not fit.
    ///
    /// `label` names the suite and its protocol version, and is hashed into the
    /// tag ahead of the domain. It is what keeps two suites over this same
    /// permutation from being the same oracle, so it is required rather than
    /// defaulted -- see the note at the top of this file.
    ///
    /// It shares one rate block with the pattern words, the domain name and the
    /// 32-byte context, so it is on a budget: 84 bytes all told, of which the
    /// present suite's patterns and domains use 14 and the context 32, leaving
    /// 38 for a label. Overrunning halts on an assertion below rather than
    /// truncating, so a long label is caught rather than silently aliased --
    /// but it is caught at run time, which is worth knowing before naming
    /// one.
    L2Sponge(
        L2Domain domain, std::span<L2IoOp const> io_pattern,
        std::span<unsigned char const, 32> context, std::string_view label);

    /// Every element must be canonical (< GOLDILOCKS_P). The callers that pack
    /// bytes get that for free; the ones absorbing integers are bounded.
    void absorb(std::span<std::uint64_t const> elems);

    void squeeze(std::span<std::uint64_t> out);

    /// Asserts the declared pattern was consumed exactly. Not a destructor:
    /// an unmet pattern is a programming error, and halting from a destructor
    /// would hide which sponge was wrong.
    void finish() const;

private:
    void permute();
    void absorb_one(std::uint64_t elem);
    std::uint64_t squeeze_one();
    void charge(bool squeeze);

    std::uint64_t st_[16]{};
    std::size_t pos_{0};
    bool squeezing_{false};
    std::span<L2IoOp const> pattern_;
    std::size_t op_{0};
    std::uint32_t done_{0};
};

/// Packs `in` at seven bytes per element, little-endian within each element,
/// zero-filling the last one. Returns the number of elements written, which is
/// ceil(len/7) and must fit `out`.
///
/// The tail is zero-padded rather than marked, because every caller carries the
/// exact length in its authenticated context -- so the encoding is injective
/// without a pad byte to get wrong.
std::size_t
l2_pack_bytes(std::span<unsigned char const> in, std::span<std::uint64_t> out);

MONAD_NAMESPACE_END
