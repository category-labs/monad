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

// secp256k1 scalar multiplication for the L2's ECDH, over two backends.
//
// On ZisK it is ziskos' zisklib, which rides the secp256k1_add and
// secp256k1_dbl precompiles and implements the GLV endomorphism -- so there is
// no curve arithmetic in this tree, only a layout conversion and the
// validations zisklib states as preconditions. At ZisK's own cost model a GLV
// multiplication is roughly 214 curve operations at 1,440 cells each
// (ARITH_EQ_COST, zisk v1.1.0-alpha -- the revision the Cargo.lock pins),
// about four Keccak-f permutations.
//
// Off ZisK it is libsecp256k1, which the host build already links. That side
// exists for the witness generator, and it means the two sides agree by TWO
// IMPLEMENTATIONS AGREEING rather than by construction, the way Poseidon2
// does. A cross-vector test is therefore not optional: if they diverge the
// only symptom is a tag that fails to verify, with nothing to say which side
// was wrong.
//
// SP1 has neither, and an L2 guest is not supported there; the build says so.

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

/// The generator. It lives here and not in the Rust bridge because zisklib's
/// `constants` module is private, so its own G is unreachable -- see the note
/// there. A transcription error would make the once-per-block sk*G == operator
/// key check fail on the first block rather than give a wrong answer quietly,
/// and l2_ecdh_self_test() checks it against zisklib's curve equation.
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

/// Both coordinates below the field size AND the curve equation satisfied, and
/// not the identity -- zisklib's stated precondition for a scalar
/// multiplication. Canonicity is tested here and not by zisklib, whose
/// is_on_curve only tests y^2 == x^3 + 7 through field operations that reduce
/// their own inputs and would accept an out-of-range coordinate.
///
/// On a point fresh out of l2_point_decompress the curve-equation half is
/// redundant: lift_x computed y as a root of x^3 + 7, so membership holds by
/// construction. It is kept anyway, and deliberately. This is a general entry
/// point -- reached with the compiled generator, and in tests with points that
/// are off the curve on purpose -- so skipping the check would mean a second,
/// unvalidated entry carrying the invariant at its seam. About 7,550 cells,
/// around one and a half percent of a transaction, is a cheap price for not
/// having an unguarded door into the code that handles the decryption key.
///
/// 7,550 rather than the three field multiplications it looks like, because
/// every Fp operation in zisklib is one arith256_mod at ARITH_EQ_COST and none
/// of them is cheaper than another: the precompile only offers a*b + c mod m,
/// so add_fp is written x*1 + y and an addition costs what a multiplication
/// does. The curve equation is four of them -- y^2, x^2, x^3, then x^3 + 7 --
/// not three and a cheap add.
bool l2_point_is_valid(L2Point const &p);

/// Non-zero and below the group order.
bool l2_scalar_is_valid(L2Scalar const &k);

/// Decompresses a 33-byte SEC1 point: a 0x02 or 0x03 tag and then x in
/// big-endian. Nullopt on any other tag, on a non-canonical x, or when x is
/// not the abscissa of a curve point -- all deterministic rejections.
///
/// The decompression IS the curve-membership check, and it is cheap -- together
/// those are why the wire carries R compressed rather than as 64 bytes.
///
/// Cheap because zisklib's sqrt does not exponentiate. It takes the root from
/// an fcall, a prover-supplied hint at FCALL_COST = 0, and verifies it with one
/// arith256_mod squaring and a canonicity assert. Lifting x is therefore about
/// four thousand cells, against the roughly 570,000 an exponentiation by
/// (p+1)/4 would have cost -- and 31 bytes of data availability are saved for
/// it.
///
/// That hint-and-verify shape is also why the canonicity tests above are not
/// overhead to be trimmed. They are the whole of what stands between a
/// prover-supplied value and a forged proof, and zisklib asserts its own
/// inside sqrt for exactly the same reason.
std::optional<L2Point>
l2_point_decompress(std::span<unsigned char const, 33> sec1);

/// The 33-byte SEC1 form of `p`. Inverse of l2_point_decompress on a valid
/// point; used by the witness generator, not by the guest.
void l2_point_compress(L2Point const &p, std::span<unsigned char, 33> sec1);

/// k*q. Nullopt when `q` fails l2_point_is_valid, `k` is zero mod n, or the
/// product is the identity. Every one of those is a deterministic REJECTION of
/// a single transaction, never a halt: the entry is consumed and the block
/// stays valid.
std::optional<L2Point> l2_ecdh(L2Scalar const &k, L2Point const &q);

/// Checks this file's constants against the backend's own curve arithmetic:
/// that G is a valid point, and that 1*G is G. Cheap, and it turns a
/// transcription slip into a named failure instead of a mismatched tag.
bool l2_ecdh_self_test();

MONAD_NAMESPACE_END
