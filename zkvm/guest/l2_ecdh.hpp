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

// L2 secp256k1 ECDH: zisklib GLV multiplication over add/dbl precompiles on
// ZisK, libsecp256k1 on the host. This layer converts layouts and enforces
// zisklib preconditions. Cross-vector tests are required because the backends
// are independent. SP1 is unsupported and rejected at build time.

#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

MONAD_NAMESPACE_BEGIN

/// A curve point in zisklib's layout: eight limbs, x in 0-3 and y in 4-7, each
/// half little-endian in its limbs so limb 0 holds the low 64 bits. Pinned
/// against zisklib's own G, which is the canonical SEC 2 generator.
struct L2Point
{
    std::uint64_t limb[8];

    friend bool operator==(L2Point const &, L2Point const &) = default;
};

/// A scalar, same limb convention.
struct L2Scalar
{
    std::uint64_t limb[4];

    friend bool operator==(L2Scalar const &, L2Scalar const &) = default;
};

/// Base field size. Transcribed from SEC 2 and cross-read against zisklib's
/// own `P`; the two agree.
inline constexpr std::uint64_t SECP256K1_P[4] = {
    0xFFFFFFFEFFFFFC2FULL,
    0xFFFFFFFFFFFFFFFFULL,
    0xFFFFFFFFFFFFFFFFULL,
    0xFFFFFFFFFFFFFFFFULL,
};

/// Scalar field size.
inline constexpr std::uint64_t SECP256K1_N[4] = {
    0xBFD25E8CD0364141ULL,
    0xBAAEDCE6AF48A03BULL,
    0xFFFFFFFFFFFFFFFEULL,
    0xFFFFFFFFFFFFFFFFULL,
};

/// Local generator constant because zisklib's constants module is private.
/// l2_ecdh_self_test checks it against the backend curve equation.
inline constexpr L2Point SECP256K1_G{
    {0x59F2815B16F81798ULL,
     0x029BFCDB2DCE28D9ULL,
     0x55A06295CE870B07ULL,
     0x79BE667EF9DCBBACULL,
     0x9C47D08FFB10D4B8ULL,
     0xFD17B448A6855419ULL,
     0x5DA4FBFC0E1108A8ULL,
     0x483ADA7726A3C465ULL}};

/// Thirty-two big-endian bytes per coordinate, x then y -- the uncompressed
/// SEC1 body without its 0x04 tag.
L2Point l2_point_from_be(std::span<unsigned char const, 64> be);
void l2_point_to_be(L2Point const &p, std::span<unsigned char, 64> be);

L2Scalar l2_scalar_from_be(std::span<unsigned char const, 32> be);

/// Require canonical coordinates, curve membership and non-identity before
/// scalar multiplication. zisklib's on-curve check reduces inputs, so it
/// cannot enforce canonicity. Retain membership checks even after
/// decompression: this general entry also accepts the compiled generator and
/// arbitrary test points.
bool l2_point_is_valid(L2Point const &p);

/// Non-zero and below the group order.
bool l2_scalar_is_valid(L2Scalar const &k);

/// Decompress SEC1 (0x02/0x03 plus big-endian x). Reject invalid tags,
/// non-canonical x and non-residues. zisklib obtains a square-root hint and
/// verifies it by squaring and checking canonicity; those checks are
/// essential because the hint is prover-supplied.
std::optional<L2Point>
l2_point_decompress(std::span<unsigned char const, 33> sec1);

/// The 33-byte SEC1 form of `p`. Inverse of l2_point_decompress on a valid
/// point; used by the witness generator, not by the guest.
void l2_point_compress(L2Point const &p, std::span<unsigned char, 33> sec1);

/// k*q, or nullopt for an invalid point/scalar or identity result. The caller
/// treats this as a rejected entry, not a block failure.
std::optional<L2Point> l2_ecdh(L2Scalar const &k, L2Point const &q);

/// Checks this file's constants against the backend's own curve arithmetic:
/// that G is a valid point, and that 1*G is G. Cheap, and it turns a
/// transcription slip into a named failure instead of a mismatched tag.
bool l2_ecdh_self_test();

MONAD_NAMESPACE_END
