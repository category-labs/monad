// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include "bn254.hpp"

namespace evmone::crypto::bn254
{
static_assert(AffinePoint{} == 0, "default constructed is the point at infinity");

bool validate(const AffinePoint& pt) noexcept
{
    const auto yy = pt.y * pt.y;
    const auto xxx = pt.x * pt.x * pt.x;
    const auto on_curve = yy == xxx + Curve::B;
    return on_curve || pt == 0;
}

AffinePoint mul(const AffinePoint& pt, const uint256& c) noexcept
{
    if (pt == 0)
        return pt;

    if (c == 0)
        return {};

    // Optimized using field endomorphism with scalar decomposition.
    // See ecc::decompose() for more details.
    const auto [k1, k2] = ecc::decompose<Curve>(c);

    const auto q = AffinePoint{Curve::BETA * pt.x, k2.sign ? -pt.y : pt.y};
    const auto p = AffinePoint{pt.x, k1.sign ? -pt.y : pt.y};
    const auto pr = msm(k1.value, p, k2.value, q);
    return ecc::to_affine(pr);
}
}  // namespace evmone::crypto::bn254
