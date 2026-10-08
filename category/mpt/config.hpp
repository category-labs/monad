// Copyright (C) 2025 Category Labs, Inc.
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

#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <type_traits>

#define MONAD_MPT_NAMESPACE_BEGIN                                              \
    MONAD_NAMESPACE_BEGIN namespace mpt                                        \
    {

#define MONAD_MPT_NAMESPACE_END                                                \
    }                                                                          \
    MONAD_NAMESPACE_END

#define MONAD_MPT_NAMESPACE ::monad::mpt

MONAD_MPT_NAMESPACE_BEGIN

static constexpr unsigned EMPTY_STRING_RLP_LENGTH = 1;
static constexpr unsigned char RLP_EMPTY_STRING = 0x80;

// Bits per trie symbol ("nibble"). 4 is the Ethereum hexary MPT. 5 gives a
// 32-ary trie for benchmarking; its node hashes keep the same keccak-of-RLP
// shape but do not match Ethereum roots. Set from CMake
// (MONAD_MPT_NIBBLE_BITS).
#ifndef MONAD_MPT_NIBBLE_BITS
    #define MONAD_MPT_NIBBLE_BITS 4
#endif
static constexpr unsigned NIBBLE_BITS = MONAD_MPT_NIBBLE_BITS;
static_assert(NIBBLE_BITS == 4 || NIBBLE_BITS == 5);
// Children per branch node.
static constexpr unsigned NIBBLE_BRANCHES = 1u << NIBBLE_BITS;

// Hash used for node references and roots: keccak256 (Ethereum) or BLAKE3,
// a benchmark option to measure how much of commit time is the hash itself.
// Set from CMake (MONAD_MPT_NODE_HASH).
#ifndef MONAD_MPT_NODE_HASH_BLAKE3
    #define MONAD_MPT_NODE_HASH_BLAKE3 0
#endif
static constexpr bool NODE_HASH_BLAKE3 = MONAD_MPT_NODE_HASH_BLAKE3 != 0;

// True only when the trie reproduces Ethereum roots: hexary with keccak.
static constexpr bool ETHEREUM_COMPATIBLE_HASHING =
    NIBBLE_BITS == 4 && !NODE_HASH_BLAKE3;
static constexpr unsigned char MAX_NIBBLE = NIBBLE_BRANCHES - 1;
// Child bitmask type: one bit per branch.
using mask_t = std::conditional_t<NIBBLE_BITS <= 4, uint16_t, uint32_t>;

// Number of symbols a byte string of `bytes` bytes expands to. The last
// symbol is zero padded when 8 * bytes is not a multiple of NIBBLE_BITS.
constexpr unsigned nibbles_for_bytes(size_t const bytes) noexcept
{
    return static_cast<unsigned>((bytes * 8 + NIBBLE_BITS - 1) / NIBBLE_BITS);
}

// Inverse of nibbles_for_bytes: the byte length a symbol string of `nibbles`
// symbols was expanded from (floor; the padding bits are dropped).
constexpr unsigned bytes_from_nibbles(unsigned const nibbles) noexcept
{
    return nibbles * NIBBLE_BITS / 8;
}

// Bytes needed to hold `bits` bits (ceil).
constexpr unsigned bytes_for_bits(unsigned const bits) noexcept
{
    return (bits + 7) / 8;
}

// Bytes needed to hold `nibbles` left-aligned symbols (ceil).
constexpr unsigned bytes_for_nibbles(unsigned const nibbles) noexcept
{
    return bytes_for_bits(nibbles * NIBBLE_BITS);
}

MONAD_MPT_NAMESPACE_END
