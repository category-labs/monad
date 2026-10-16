// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2024 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include "fields.hpp"

namespace evmone::crypto::bn254
{
/// Defines coefficients needed for fast Frobenius endomorphism computation.
/// For more ref see https://eprint.iacr.org/2010/354.pdf 3.2 Frobenius Operator.
inline constexpr std::array<std::array<Fq2, 5>, 3> FROBENIUS_COEFFS = {{
    {{
        {0x1284b71c2865a7dfe8b99fdd76e68b605c521e08292f2176d60b35dadcc9e470_u256,
            0x246996f3b4fae7e6a6327cfe12150b8e747992778eeec7e5ca5cf05f80f362ac_u256},
        {0x2fb347984f7911f74c0bec3cf559b143b78cc310c2c3330c99e39557176f553d_u256,
            0x16c9e55061ebae204ba4cc8bd75a079432ae2a1d0b7c9dce1665d51c640fcba2_u256},
        {0x63cf305489af5dcdc5ec698b6e2f9b9dbaae0eda9c95998dc54014671a0135a_u256,
            0x7c03cbcac41049a0704b5a7ec796f2b21807dc98fa25bd282d37f632623b0e3_u256},
        {0x5b54f5e64eea80180f3c0b75a181e84d33365f7be94ec72848a1f55921ea762_u256,
            0x2c145edbe7fd8aee9f3a80b03b0b1c923685d2ea1bdec763c13b4711cd2b8126_u256},
        {0x183c1e74f798649e93a3661a4353ff4425c459b55aa1bd32ea2c810eab7692f_u256,
            0x12acf2ca76fd0675a27fb246c7729f7db080cb99678e2ac024c6b8ee6e0c2c4b_u256},
    }},
    {{
        {0x30644e72e131a0295e6dd9e7e0acccb0c28f069fbb966e3de4bd44e5607cfd49_u256, 0_u256},
        {0x30644e72e131a0295e6dd9e7e0acccb0c28f069fbb966e3de4bd44e5607cfd48_u256, 0_u256},
        {0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46_u256, 0_u256},
        {0x000000000000000059e26bcea0d48bacd4f263f1acdb5c4f5763473177fffffe_u256, 0_u256},
        {0x000000000000000059e26bcea0d48bacd4f263f1acdb5c4f5763473177ffffff_u256, 0_u256},
    }},
    {{
        {0x19dc81cfcc82e4bbefe9608cd0acaa90894cb38dbe55d24ae86f7d391ed4a67f_u256,
            0xabf8b60be77d7306cbeee33576139d7f03a5e397d439ec7694aa2bf4c0c101_u256},
        {0x856e078b755ef0abaff1c77959f25ac805ffd3d5d6942d37b746ee87bdcfb6d_u256,
            0x4f1de41b3d1766fa9f30e6dec26094f0fdf31bf98ff2631380cab2baaa586de_u256},
        {0x2a275b6d9896aa4cdbf17f1dca9e5ea3bbd689a3bea870f45fcc8ad066dce9ed_u256,
            0x28a411b634f09b8fb14b900e9507e9327600ecc7d8cf6ebab94d0cb3b2594c64_u256},
        {0xbc58c6611c08dab19bee0f7b5b2444ee633094575b06bcb0e1a92bc3ccbf066_u256,
            0x23d5e999e1910a12feb0f6ef0cd21d04a44a9e08737f96e55fe3ed9d730c239f_u256},
        {0x13c49044952c0905711699fa3b4d3f692ed68098967c84a5ebde847076261b43_u256,
            0x16db366a59b1dd0b9fb1b2282a48633d3e2ddaea200280211f25041384282499_u256},
    }},
}};

/// Verifies that affine point over Fq^2 field is on the twisted curve.
constexpr bool is_on_twisted_curve(const ecc::AffinePoint<E2>& p) noexcept
{
    const auto x3 = p.x * p.x * p.x;
    const auto y2 = p.y * p.y;

    return y2 == x3 + E2::B;
}

// Frobenius endomorphism related functions are implemented based on
// https://hackmd.io/@jpw/bn254#mathbb-G_2-membership-check-using-efficient-endomorphism
// and
// https://eprint.iacr.org/2010/354.pdf 3.2 Frobenius Operator

/// Computes Frobenius endomorphism of point `p` in Jacobian coordinates from twisted curve
/// over Fq2 extended field.
/// This specialisation computes Frobenius and Frobenius^3
/// TODO: add reference that it's exactly the same as untwist->frobenius->twist
template <int P>
constexpr ecc::ProjPoint<E2> endomorphism(const ecc::ProjPoint<E2>& p) noexcept
    requires(P == 1 || P == 3)
{
    return {
        p.x.conjugate() * FROBENIUS_COEFFS[P - 1][1],
        p.y.conjugate() * FROBENIUS_COEFFS[P - 1][2],
        p.z.conjugate(),
    };
}

/// Computes Frobenius endomorphism of point `p` in Jacobian coordinates from twisted curve
/// over Fq^2 extended field.
/// This specialisation computes Frobenius^2
template <int P>
constexpr ecc::ProjPoint<E2> endomorphism(const ecc::ProjPoint<E2>& p) noexcept
    requires(P == 2)
{
    return {
        p.x * FROBENIUS_COEFFS[1][1],
        p.y * FROBENIUS_COEFFS[1][2],
        p.z,
    };
}

/// Computes Frobenius endomorphism of point `p` in affine coordinates from twisted curve
/// over Fq^2 extended field.
/// This specialisation computes Frobenius and Frobenius^3
template <int P>
constexpr ecc::AffinePoint<E2> endomorphism(const ecc::AffinePoint<E2>& p) noexcept
    requires(P == 1 || P == 3)
{
    return {
        p.x.conjugate() * FROBENIUS_COEFFS[P - 1][1],
        p.y.conjugate() * FROBENIUS_COEFFS[P - 1][2],
    };
}

/// Computes Frobenius endomorphism of point `p` in affine coordinates from twisted curve
/// over Fq^2 extended field.
/// This specialisation computes Frobenius^2
template <int P>
constexpr ecc::AffinePoint<E2> endomorphism(const ecc::AffinePoint<E2>& p) noexcept
    requires(P == 2)
{
    return {
        p.x * FROBENIUS_COEFFS[1][1],
        p.y * FROBENIUS_COEFFS[1][2],
    };
}

/// Computes Frobenius endomorphism for Fq12 field member values
/// This specialisation computes Frobenius and Frobenius^3
template <int P>
constexpr Fq12 endomorphism(const Fq12& f) noexcept
    requires(P == 1 || P == 3)
{
    return Fq12({
        Fq6({
            f.coeffs[0].coeffs[0].conjugate(),
            f.coeffs[0].coeffs[1].conjugate() * FROBENIUS_COEFFS[P - 1][1],
            f.coeffs[0].coeffs[2].conjugate() * FROBENIUS_COEFFS[P - 1][3],
        }),
        Fq6({
            f.coeffs[1].coeffs[0].conjugate() * FROBENIUS_COEFFS[P - 1][0],
            f.coeffs[1].coeffs[1].conjugate() * FROBENIUS_COEFFS[P - 1][2],
            f.coeffs[1].coeffs[2].conjugate() * FROBENIUS_COEFFS[P - 1][4],
        }),
    });
}

/// Computes Frobenius operator for Fq12 field member values
/// This specialization computes Frobenius^2
template <int P>
constexpr Fq12 endomorphism(const Fq12& f) noexcept
    requires(P == 2)
{
    return Fq12({
        Fq6({
            f.coeffs[0].coeffs[0],
            f.coeffs[0].coeffs[1] * FROBENIUS_COEFFS[1][1],
            f.coeffs[0].coeffs[2] * FROBENIUS_COEFFS[1][3],
        }),
        Fq6({
            f.coeffs[1].coeffs[0] * FROBENIUS_COEFFS[1][0],
            f.coeffs[1].coeffs[1] * FROBENIUS_COEFFS[1][2],
            f.coeffs[1].coeffs[2] * FROBENIUS_COEFFS[1][4],
        }),
    });
}

/// Computes `P0 + P1` in Jacobian coordinates.
/// P0 and P1 must not be the point at infinity, and must not be equal or negations of each other.
constexpr ecc::ProjPoint<E2> add(
    const ecc::ProjPoint<E2>& P0, const ecc::ProjPoint<E2>& P1) noexcept
{
    const auto& x0 = P0.x;
    const auto& y0 = P0.y;
    const auto& z0 = P0.z;

    const auto& x1 = P1.x;
    const auto& y1 = P1.y;
    const auto& z1 = P1.z;

    const auto z0_squared = z0 * z0;
    const auto z0_cubed = z0 * z0_squared;

    const auto z1_squared = z1 * z1;
    const auto z1_cubed = z1 * z1_squared;

    const auto U1 = x0 * z1_squared;
    const auto U2 = x1 * z0_squared;
    const auto S1 = y0 * z1_cubed;
    const auto S2 = y1 * z0_cubed;
    const auto H = U2 - U1;  // x1 * z0^2 - x0 * z1^2
    const auto R = S2 - S1;  // y1 * z0^3 - y0 * z1 ^3

    const auto H_squared = H * H;
    const auto H_cubed = H * H_squared;
    const auto R_squared = R * R;

    const auto V = U1 * H_squared;

    const auto X3 = R_squared - H_cubed - (V + V);
    const auto Y3 = R * (V - X3) - S1 * H_cubed;
    const auto Z3 = H * z0 * z1;

    return {X3, Y3, Z3};
}

/// Computes `N` doubles of the point `a` in Jacobian coordinates.
template <int N>
constexpr ecc::ProjPoint<E2> n_dbl(const ecc::ProjPoint<E2>& a) noexcept
{
    auto r = dbl(a);
    for (int i = 0; i < N - 1; ++i)
        r = dbl(r);

    return r;
}

/// Addchain generated algorithm which multiplies point `a` in Jacobian coordinated
/// by X (curve seed).
constexpr ecc::ProjPoint<E2> mul_by_X(const ecc::ProjPoint<E2>& a) noexcept
{
    auto t0 = dbl(a);
    auto t2 = dbl(t0);
    auto c = dbl(t2);
    auto t4 = dbl(c);
    auto t6 = add(a, t4);
    t4 = add(t6, t0);
    auto t8 = add(a, t4);
    auto t10 = add(c, t6);
    auto t12 = dbl(t6);
    t8 = add(t8, t4);
    t4 = add(t8, t0);
    t12 = n_dbl<6>(t12);
    t2 = add(t12, t2);
    t2 = add(t2, t10);
    t2 = n_dbl<7>(t2);
    t10 = add(t2, t10);
    t10 = n_dbl<8>(t10);
    t10 = add(t10, t4);
    t0 = add(t10, t0);
    t0 = n_dbl<6>(t0);
    t6 = add(t0, t6);
    t6 = n_dbl<8>(t6);
    t6 = add(t6, t4);
    t6 = n_dbl<6>(t6);
    t6 = add(t6, t4);
    t6 = n_dbl<10>(t6);
    t8 = add(t6, t8);
    t8 = n_dbl<6>(t8);
    t4 = add(t4, t8);
    c = add(t4, c);

    return c;
}

/// Checks that point `p_aff` is in proper subgroup of points from twisted curve over Fq2 field.
/// For more details see https://eprint.iacr.org/2022/348.pdf Example 1 from 3.1.2 Examples
constexpr bool g2_subgroup_check(const ecc::AffinePoint<E2>& p_aff) noexcept
{
    const auto p = ecc::ProjPoint<E2>{p_aff};

    const auto px = mul_by_X(p);
    const auto px1 = add(px, p);
    const auto _2px = dbl(px);

    const auto e_px = endomorphism<1>(px);
    const auto ee_px = endomorphism<2>(px);
    const auto eee_2px = endomorphism<3>(_2px);

    const auto l = add(add(px1, e_px), ee_px);

    return l == eee_2px;
}

/// Computes point Q doubling for twisted curve + line tangent (in untwisted Q) to
/// the curve (not twisted curve) evaluated at point P
/// Returns live evaluation coefficients (-t, tw, tvw)
/// For more details see https://notes.ethereum.org/@ipsilon/Hkn2a2qk0
constexpr ecc::ProjPoint<E2> lin_func_and_dbl(
    const ecc::ProjPoint<E2>& Q, std::array<Fq2, 3>& t) noexcept
{
    const auto& x = Q.x;
    const auto& y = Q.y;
    const auto& z = Q.z;

    const auto y_squared = y * y;
    const auto x_squared = x * x;
    const auto z_squared = z * z;
    const auto y_4 = y_squared * y_squared;
    const auto _4y_4 = y_4 + y_4 + y_4 + y_4;

    const auto R = y_squared + y_squared;
    const auto A = (x + R);
    const auto S = A * A - x_squared - _4y_4;  // 2xR = (x+R)^2 - x^2 - R^2
    const auto M = x_squared + x_squared + x_squared;

    const auto N = y + z;

    const auto Xp = M * M - (S + S);
    const auto Yp = M * (S - Xp) - (_4y_4 + _4y_4);
    const auto Zp = N * N - y_squared - z_squared;  // 2yz = (y+z)^2 - y^2 - z^2

    t[0] = Zp * z_squared;
    t[1] = M * z_squared;
    t[2] = R - M * x;

    return ecc::ProjPoint<E2>{Xp, Yp, Zp};
}

/// Computes points P0 and P1 addition for twisted curve + line defined by untwisted P1 and P2
/// points on the curve (not twisted curve) evaluated at point P. Formula is simplified for P1.z
/// == 1. For more details see https://notes.ethereum.org/@ipsilon/Hkn2a2qk0
[[nodiscard]] constexpr ecc::ProjPoint<E2> lin_func_and_add(
    const ecc::ProjPoint<E2>& P0, const ecc::AffinePoint<E2>& P1, std::array<Fq2, 3>& t) noexcept
{
    const auto& x0 = P0.x;
    const auto& y0 = P0.y;
    const auto& z0 = P0.z;

    const auto& x1 = P1.x;
    const auto& y1 = P1.y;

    const auto z0_squared = z0 * z0;
    const auto z0_cubed = z0 * z0_squared;

    const auto U2 = x1 * z0_squared;
    const auto S2 = y1 * z0_cubed;
    const auto H = U2 - x0;  // x1 * z0^2 - x0 * z1^2
    const auto R = S2 - y0;  // y1 * z0^3 - y0 * z1^3

    const auto H_squared = H * H;
    const auto H_cubed = H * H_squared;
    const auto R_squared = R * R;

    const auto V = x0 * H_squared;

    const auto X3 = R_squared - H_cubed - (V + V);
    const auto Y3 = R * (V - X3) - y0 * H_cubed;
    const auto Z3 = H * z0;

    t[0] = -H * z0_cubed;   // = x0·z0³ − U2·z0³
    t[1] = R * z0_squared;  // = S2·z0² − y0·z0²
    t[2] = y0 * U2 - x0 * S2;

    return ecc::ProjPoint<E2>{X3, Y3, Z3};
}

/// Computes points P0 and P1 addition for twisted curve + line defined by untwisted P1 and P2
/// points on the curve (not twisted curve) evaluated at point P. Formula is simplified for P1.z
/// == 1. For more details see https://notes.ethereum.org/@ipsilon/Hkn2a2qk0
constexpr void lin_func(
    const ecc::ProjPoint<E2>& P0, const ecc::AffinePoint<E2>& P1, std::array<Fq2, 3>& t) noexcept
{
    const auto& x0 = P0.x;
    const auto& y0 = P0.y;
    const auto& z0 = P0.z;

    const auto& x1 = P1.x;
    const auto& y1 = P1.y;

    const auto z0_squared = z0 * z0;
    const auto z0_cubed = z0 * z0_squared;

    const auto U2 = x1 * z0_squared;
    const auto S2 = y1 * z0_cubed;

    t[0] = (x0 - U2) * z0_cubed;    // = x0·z0³ − U2·z0³
    t[1] = (S2 - y0) * z0_squared;  // = S2·z0² − y0·z0²
    t[2] = y0 * U2 - x0 * S2;
}

/// Computes f^2 for f in Fq12. For more ref https://eprint.iacr.org/2010/354.pdf Algorithm 22
[[nodiscard]] constexpr Fq12 square(const Fq12& f) noexcept
{
    const Fq2& ksi = Fq6Config::ksi;

    const auto& a0 = f.coeffs[0];
    const auto& a1 = f.coeffs[1];
    auto c0 = a0 - a1;
    auto c3 = a0 - Fq6({ksi * a1.coeffs[2], a1.coeffs[0], a1.coeffs[1]});
    auto c2 = a0 * a1;
    c0 = c0 * c3 + c2;
    const auto c1 = c2 + c2;
    c2 = Fq6({ksi * c2.coeffs[2], c2.coeffs[0], c2.coeffs[1]});
    c0 = c0 + c2;

    return Fq12({c0, c1});
}

/// Computes `a^2` for `a` from `Fq^4 = Fq^2[V](V^2 - ksi)` where `V` is from Fq^2 extended field.
/// For more reference see https://eprint.iacr.org/2010/354.pdf Algorithm 9
constexpr std::pair<Fq2, Fq2> fq4_square(const std::pair<Fq2, Fq2>& a) noexcept
{
    const auto& a0 = a.first;
    const auto& a1 = a.second;

    const auto t0 = a0 * a0;
    const auto t1 = a1 * a1;

    const auto c0 = t1 * Fq6Config::ksi + t0;
    auto c1 = a0 + a1;
    c1 = c1 * c1 - t0 - t1;

    return {c0, c1};
}

/// Computes `c^2` for `x` from Fq^12 where `x^(FieldPrime^6 - 1) == 1`.
/// This is Fq^12 subgroup called cyclotomic polynomials or group of `r` roots of unity.
constexpr Fq12 cyclotomic_square(const Fq12& c) noexcept
{
    const auto& g = c.coeffs[0];
    const auto& h = c.coeffs[1];

    const auto& g0 = g.coeffs[0];
    const auto& g1 = g.coeffs[1];
    const auto& g2 = g.coeffs[2];

    const auto& h0 = h.coeffs[0];
    const auto& h1 = h.coeffs[1];
    const auto& h2 = h.coeffs[2];

    const auto [t00, t11] = fq4_square({g0, h1});
    const auto [t01, t12] = fq4_square({h0, g2});  // Typo in paper t01 <-> t12
    const auto [t02, aux] = fq4_square({g1, h2});

    const auto t10 = aux * Fq6Config::ksi;

    const auto c00 = (t00 + t00 + t00) - (g0 + g0);
    const auto c01 = (t01 + t01 + t01) - (g1 + g1);
    const auto c02 = (t02 + t02 + t02) - (g2 + g2);

    const auto c10 = h0 + h0 + t10 + t10 + t10;
    const auto c11 = h1 + h1 + t11 + t11 + t11;
    const auto c12 = h2 + h2 + t12 + t12 + t12;

    return Fq12({Fq6({c00, c01, c02}), Fq6({c10, c11, c12})});
}

/// Computes `cyclotomic_square` N times.
template <int N>
constexpr Fq12 n_cyclotomic_square(const Fq12& c) noexcept
{
    auto r = c;
    for (int i = 0; i < N; ++i)
        r = cyclotomic_square(r);

    return r;
}

/// Computes `a^X` where `X` is the curve seed parameter
/// and `a` is from cyclotomic subgroup of Fq^12.
constexpr Fq12 cyclotomic_pow_to_X(const Fq12& a) noexcept
{
    auto t0 = cyclotomic_square(a);
    auto t2 = cyclotomic_square(t0);
    auto c = cyclotomic_square(t2);
    auto t4 = cyclotomic_square(c);
    auto t6 = a * t4;
    t4 = t6 * t0;
    auto t8 = a * t4;
    auto t10 = c * t6;
    auto t12 = cyclotomic_square(t6);
    t8 = t8 * t4;
    t4 = t8 * t0;
    t12 = n_cyclotomic_square<6>(t12);
    t2 = t12 * t2;
    t2 = t2 * t10;
    t2 = n_cyclotomic_square<7>(t2);
    t10 = t2 * t10;
    t10 = n_cyclotomic_square<8>(t10);
    t10 = t10 * t4;
    t0 = t10 * t0;
    t0 = n_cyclotomic_square<6>(t0);
    t6 = t0 * t6;
    t6 = n_cyclotomic_square<8>(t6);
    t6 = t6 * t4;
    t6 = n_cyclotomic_square<6>(t6);
    t6 = t6 * t4;
    t6 = n_cyclotomic_square<10>(t6);
    t8 = t6 * t8;
    t8 = n_cyclotomic_square<6>(t8);
    t4 = t4 * t8;
    c = t4 * c;

    return c;
}

}  // namespace evmone::crypto::bn254
