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

// See l2_ecdh.hpp for the two backends and why the cross-vector test matters.

#include <zkvm/guest/l2_ecdh.hpp>

#include <category/core/assert.h>
#include <category/core/int.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>

#if defined(MONAD_ZKVM_SP1)
    // There is no Poseidon2 precompile on SP1 and no secp256k1 curve backend
    // either: zisklib is ZisK's, and libsecp256k1 is not linkable bare-metal.
    // Writing a software curve to make the arm exist would measure that
    // software curve, not this protocol.
    #error "MONAD_ZKVM_L2 is not supported on SP1: no secp256k1 backend"
#endif

#ifdef MONAD_ZKVM_ZISK
extern "C" int monad_zkvm_secp256k1_mul(
    std::uint64_t const *k, std::uint64_t const *q, std::uint64_t *out);
extern "C" int monad_zkvm_secp256k1_is_valid(std::uint64_t const *q);
extern "C" int monad_zkvm_secp256k1_lift_x(
    std::uint64_t const *x, int y_is_odd, std::uint64_t *out);
#else
    #include <secp256k1.h>

    #include <memory>
#endif

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Limb 0 is the low 64 bits, so it comes from the LAST eight bytes.
void limbs_from_be(std::uint64_t *const out, unsigned char const *const be)
{
    for (std::size_t i = 0; i < 4; ++i) {
        out[i] = load_be_unsafe<std::uint64_t>(be + (3 - i) * 8);
    }
}

void limbs_to_be(unsigned char *const be, std::uint64_t const *const in)
{
    for (std::size_t i = 0; i < 4; ++i) {
        store_be(be + (3 - i) * 8, in[i]);
    }
}

/// Little-endian limbs, most significant first.
bool lt_256(std::uint64_t const *const a, std::uint64_t const *const b)
{
    for (std::size_t i = 4; i-- > 0;) {
        if (a[i] != b[i]) {
            return a[i] < b[i];
        }
    }
    return false;
}

bool is_zero_256(std::uint64_t const *const a)
{
    return (a[0] | a[1] | a[2] | a[3]) == 0;
}

/// The curve equation and non-identity, from whichever backend is linked.
/// Canonicity is the caller's and is already done by the time this runs.
bool on_curve(L2Point const &p)
{
#ifdef MONAD_ZKVM_ZISK
    return monad_zkvm_secp256k1_is_valid(p.limb) == 0;
#else
    unsigned char ser[65];
    ser[0] = 0x04;
    limbs_to_be(ser + 1, p.limb);
    limbs_to_be(ser + 33, p.limb + 4);
    thread_local std::
        unique_ptr<secp256k1_context, void (*)(secp256k1_context *)> const ctx(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);
    secp256k1_pubkey pk;
    // Parsing rejects the identity and anything off the curve; it also rejects
    // out-of-range coordinates, which is a second line behind the caller's own
    // canonicity test rather than a substitute for it.
    return secp256k1_ec_pubkey_parse(ctx.get(), &pk, ser, sizeof(ser)) == 1;
#endif
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

L2Point l2_point_from_be(std::span<unsigned char const, 64> const be)
{
    L2Point p{};
    limbs_from_be(p.limb, be.data());
    limbs_from_be(p.limb + 4, be.data() + 32);
    return p;
}

void l2_point_to_be(L2Point const &p, std::span<unsigned char, 64> const be)
{
    limbs_to_be(be.data(), p.limb);
    limbs_to_be(be.data() + 32, p.limb + 4);
}

L2Scalar l2_scalar_from_be(std::span<unsigned char const, 32> const be)
{
    L2Scalar k{};
    limbs_from_be(k.limb, be.data());
    return k;
}

bool l2_point_is_valid(L2Point const &p)
{
    // Canonicity first, and on the coordinates rather than on a reduced form:
    // a coordinate at or above the field size is not a point, and zisklib's
    // is_on_curve would reduce it and answer about a different point.
    if (!lt_256(p.limb, SECP256K1_P) || !lt_256(p.limb + 4, SECP256K1_P)) {
        return false;
    }
    if (is_zero_256(p.limb) && is_zero_256(p.limb + 4)) {
        return false;
    }
    return on_curve(p);
}

bool l2_scalar_is_valid(L2Scalar const &k)
{
    return !is_zero_256(k.limb) && lt_256(k.limb, SECP256K1_N);
}

std::optional<L2Point> l2_ecdh(L2Scalar const &k, L2Point const &q)
{
    if (!l2_scalar_is_valid(k) || !l2_point_is_valid(q)) {
        return std::nullopt;
    }
#ifdef MONAD_ZKVM_ZISK
    L2Point out{};
    if (monad_zkvm_secp256k1_mul(k.limb, q.limb, out.limb) != 0) {
        return std::nullopt;
    }
    return out;
#else
    unsigned char ser[65];
    ser[0] = 0x04;
    l2_point_to_be(q, std::span<unsigned char, 64>{ser + 1, 64});

    thread_local std::
        unique_ptr<secp256k1_context, void (*)(secp256k1_context *)> const ctx(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);

    secp256k1_pubkey pk;
    if (secp256k1_ec_pubkey_parse(ctx.get(), &pk, ser, sizeof(ser)) != 1) {
        return std::nullopt;
    }
    unsigned char tweak[32];
    limbs_to_be(tweak, k.limb);
    // Fails on a tweak outside [1, n-1] or a product at infinity -- the same
    // two rejections the ZisK path returns FAIL for.
    if (secp256k1_ec_pubkey_tweak_mul(ctx.get(), &pk, tweak) != 1) {
        return std::nullopt;
    }
    std::size_t len = sizeof(ser);
    MONAD_ASSERT(
        secp256k1_ec_pubkey_serialize(
            ctx.get(), ser, &len, &pk, SECP256K1_EC_UNCOMPRESSED) == 1);
    MONAD_ASSERT(len == sizeof(ser) && ser[0] == 0x04);
    return l2_point_from_be(std::span<unsigned char const, 64>{ser + 1, 64});
#endif
}

std::optional<L2Point>
l2_point_decompress(std::span<unsigned char const, 33> const sec1)
{
    if (sec1[0] != 0x02 && sec1[0] != 0x03) {
        return std::nullopt;
    }
    bool const y_is_odd = sec1[0] == 0x03;

    L2Point p{};
    limbs_from_be(p.limb, sec1.data() + 1);
    // Checked here rather than left to the backend: a non-canonical x would be
    // reduced by the field arithmetic and answer about a different point.
    if (!lt_256(p.limb, SECP256K1_P)) {
        return std::nullopt;
    }

#ifdef MONAD_ZKVM_ZISK
    // A distinct destination: passing p.limb as both operands would leave a
    // live shared reference aliasing what the bridge writes through.
    L2Point lifted{};
    if (monad_zkvm_secp256k1_lift_x(p.limb, y_is_odd ? 1 : 0, lifted.limb) !=
        0) {
        return std::nullopt;
    }
    return lifted;
#else
    thread_local std::
        unique_ptr<secp256k1_context, void (*)(secp256k1_context *)> const ctx(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);
    secp256k1_pubkey pk;
    if (secp256k1_ec_pubkey_parse(ctx.get(), &pk, sec1.data(), sec1.size()) !=
        1) {
        return std::nullopt;
    }
    unsigned char ser[65];
    std::size_t len = sizeof(ser);
    MONAD_ASSERT(
        secp256k1_ec_pubkey_serialize(
            ctx.get(), ser, &len, &pk, SECP256K1_EC_UNCOMPRESSED) == 1);
    return l2_point_from_be(std::span<unsigned char const, 64>{ser + 1, 64});
#endif
}

void l2_point_compress(
    L2Point const &p, std::span<unsigned char, 33> const sec1)
{
    sec1[0] = static_cast<unsigned char>((p.limb[4] & 1u) ? 0x03 : 0x02);
    limbs_to_be(sec1.data() + 1, p.limb);
}

bool l2_ecdh_self_test()
{
    if (!l2_point_is_valid(SECP256K1_G)) {
        return false;
    }
    L2Scalar const one{{1, 0, 0, 0}};
    auto const g = l2_ecdh(one, SECP256K1_G);
    if (!g.has_value() || *g != SECP256K1_G) {
        return false;
    }
    unsigned char sec1[33];
    l2_point_compress(SECP256K1_G, std::span<unsigned char, 33>{sec1});
    auto const back =
        l2_point_decompress(std::span<unsigned char const, 33>{sec1});
    return back.has_value() && *back == SECP256K1_G;
}

MONAD_NAMESPACE_END
