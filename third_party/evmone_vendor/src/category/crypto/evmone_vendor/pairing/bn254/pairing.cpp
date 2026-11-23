// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2024 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include "../../bn254.hpp"
#include "fields.hpp"
#include "utils.hpp"

namespace evmone::crypto::bn254
{
namespace
{
/// Multiplies `fr` (Fq12) values by sparse `v` (Fq12) value of the form
/// [[t[0] * y, 0, 0],[t[1] * x, t[2], 0]] where `v` coefficients are from Fq2
constexpr void multiply_by_lin_func_value(
    Fq12& fr, const std::array<Fq2, 3>& t, const Fq& x, const Fq& y) noexcept
{
    const Fq12 f = fr;
    const auto& ksi = Fq6Config::ksi;

    const auto t0y = t[0] * y;
    const auto t1x = t[1] * x;
    const auto t2ksi = t[2] * ksi;

    fr.coeffs[0].coeffs[0] = f.coeffs[0].coeffs[0] * t0y + f.coeffs[1].coeffs[2] * t1x * ksi +
                             f.coeffs[1].coeffs[1] * t2ksi;
    fr.coeffs[0].coeffs[1] =
        f.coeffs[0].coeffs[1] * t0y + f.coeffs[1].coeffs[0] * t1x + f.coeffs[1].coeffs[2] * t2ksi;
    fr.coeffs[0].coeffs[2] =
        f.coeffs[0].coeffs[2] * t0y + f.coeffs[1].coeffs[1] * t1x + f.coeffs[1].coeffs[0] * t[2];
    fr.coeffs[1].coeffs[0] =
        f.coeffs[1].coeffs[0] * t0y + f.coeffs[0].coeffs[0] * t1x + f.coeffs[0].coeffs[2] * t2ksi;
    fr.coeffs[1].coeffs[1] =
        f.coeffs[1].coeffs[1] * t0y + f.coeffs[0].coeffs[1] * t1x + f.coeffs[0].coeffs[0] * t[2];
    fr.coeffs[1].coeffs[2] =
        f.coeffs[1].coeffs[2] * t0y + f.coeffs[0].coeffs[2] * t1x + f.coeffs[0].coeffs[1] * t[2];
}

/// The signed digits of the ate loop count 6x+2 = 29793968203157093288, most significant first,
/// with the leading 1 omitted. This is a semi-NAF: adjacent non-zeros occur only at the leading
/// 1, 1, which the non-adjacent form spells as 1, 0, -1. Both have 22 non-zero digits, but this
/// one is a digit shorter, i.e. one loop iteration less.
// clang-format off
inline constexpr int8_t ATE_LOOP_COUNT_DIGITS[] = {
     1,  0,  1,  0,  0,  0, -1,  0, -1,  0,  0,  0, -1,  0,  1,  0,
    -1,  0,  0, -1,  0,  0,  0,  0,  0,  1,  0,  0, -1,  0,  1,  0,
     0, -1,  0,  0,  0,  0, -1,  0,  1,  0,  0,  0, -1,  0, -1,  0,
     0,  1,  0,  0,  0, -1,  0,  0, -1,  0,  1,  0,  1,  0,  0,  0,
};
// clang-format on

/// Miller loop for all the pairs at once,
/// according to https://eprint.iacr.org/2010/354.pdf Algorithm 1.
Fq12 multi_miller_loop(std::span<const std::pair<AffinePoint, ExtPoint>> pairs) noexcept
{
    // The running point of every pair; starting at Q applies the omitted leading digit 1.
    // TODO: Avoid the allocation: at most 492 pairs fit the transaction gas limit (EIP-7825).
    // TODO: Caching -Q and -P.y next to the running points may be beneficial.
    std::vector<ecc::ProjPoint<E2>> Ts;
    Ts.reserve(pairs.size());
    for (const auto& [_, Q] : pairs)
        Ts.emplace_back(Q);

    auto f = Fq12::one();
    std::array<Fq2, 3> t;

    for (const auto digit : ATE_LOOP_COUNT_DIGITS)
    {
        // The f <- f^2 * line recurrence is multiplicative over the pairs, so a single
        // accumulator serves them all: one squaring per iteration instead of one per pair.
        f = square(f);

        for (size_t j = 0; j != pairs.size(); ++j)
        {
            const auto& [P, Q] = pairs[j];
            if (P == 0 || Q == 0)  // A pair with a point at infinity contributes 1.
                continue;

            auto& T = Ts[j];
            T = lin_func_and_dbl(T, t);
            multiply_by_lin_func_value(f, t, P.x, -P.y);

            if (digit != 0)
            {
                T = lin_func_and_add(T, digit > 0 ? Q : -Q, t);
                multiply_by_lin_func_value(f, t, P.x, P.y);
            }
        }
    }

    for (size_t j = 0; j != pairs.size(); ++j)
    {
        const auto& [P, Q] = pairs[j];
        if (P == 0 || Q == 0)
            continue;

        // Frobenius endomorphism for point Q from twisted curve over Fq2 field.
        // It's essentially untwist -> frobenius -> twist chain of transformation.
        const auto Q1 = endomorphism<1>(Q);

        // Similar to above one. It makes untwist -> frobenius^2 -> twist transformation plus
        // negation according to miller loop spec.
        const auto nQ2 = -endomorphism<2>(Q);

        auto& T = Ts[j];
        T = lin_func_and_add(T, Q1, t);
        multiply_by_lin_func_value(f, t, P.x, P.y);

        lin_func(T, nQ2, t);
        multiply_by_lin_func_value(f, t, P.x, P.y);
    }

    return f;
}

/// Final exponentiation formula.
/// Based on https://eprint.iacr.org/2010/354.pdf 4.2 Algorithm 31.
Fq12 final_exp(const Fq12& v) noexcept
{
    auto f = v;
    auto f1 = f.conjugate();

    f = f1 * f.inv();            // easy 1
    f = endomorphism<2>(f) * f;  // easy 2

    f1 = f.conjugate();

    const auto ft1 = cyclotomic_pow_to_X(f);
    const auto ft2 = cyclotomic_pow_to_X(ft1);
    const auto ft3 = cyclotomic_pow_to_X(ft2);
    const auto fp1 = endomorphism<1>(f);
    const auto fp2 = endomorphism<2>(f);
    const auto fp3 = endomorphism<3>(f);
    const auto y0 = fp1 * fp2 * fp3;
    const auto y1 = f1;
    const auto y2 = endomorphism<2>(ft2);
    const auto y3 = endomorphism<1>(ft1).conjugate();
    const auto y4 = (endomorphism<1>(ft2) * ft1).conjugate();
    const auto y5 = ft2.conjugate();
    const auto y6 = (endomorphism<1>(ft3) * ft3).conjugate();

    auto t0 = cyclotomic_square(y6) * y4 * y5;
    auto t1 = y3 * y5 * t0;
    t0 = t0 * y2;
    t1 = cyclotomic_square(t1) * t0;
    t1 = cyclotomic_square(t1);
    t0 = t1 * y1;
    t1 = t1 * y0;
    t0 = cyclotomic_square(t0);
    return t1 * t0;
}
}  // namespace

std::optional<bool> pairing_check(std::span<const std::pair<AffinePoint, ExtPoint>> pairs) noexcept
{
    if (pairs.empty())
        return true;

    for (const auto& [p, q] : pairs)
    {
        if (!validate(p))
            return std::nullopt;

        // Verify that Q is on the curve and in the proper subgroup. This subgroup is much smaller
        // than the group containing all the points from the twisted curve over Fq2 field.
        // TODO: Fold q != 0 check into curve/subgroup checks.
        if (q != 0 && (!is_on_twisted_curve(q) || !g2_subgroup_check(q)))
            return std::nullopt;
    }

    return final_exp(multi_miller_loop(pairs)) == Fq12::one();
}
}  // namespace evmone::crypto::bn254
