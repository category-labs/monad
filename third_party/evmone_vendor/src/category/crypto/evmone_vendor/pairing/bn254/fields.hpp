// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2024 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include "../../bn254.hpp"
#include "../../ecc.hpp"
#include "../field_template.hpp"

namespace evmone::crypto::bn254
{
using namespace intx;

// Extension fields implemented based on https://hackmd.io/@jpw/bn254#Field-extension-towers
// Fq, Fq2Config, Fq2, and E2 live in bn254.hpp to be reachable from the precompile boundary.

/// Specifies Fq^6 extension field for bn254 curve. Fq^2 field extended with irreducible
/// `v^3 - (9 + u)` polynomial over the Fq^2 field. `v` is the Fq^6 field element.
struct Fq6Config
{
    using BaseFieldT = Fq;
    using ValueT = Fq2;
    static constexpr uint8_t DEGREE = 3;
    static constexpr auto ksi = Fq2({Fq(9_u256), Fq(1_u256)});
};
using Fq6 = ecc::ExtFieldElem<Fq6Config>;

/// Specifies Fq^12 extension field for bn254 curve. Fq^6 field extended with irreducible
/// `w^2 - v` polynomial over the Fq^2 field. `v` is the Fq^6 field element.
/// `w` is Fq^12 field element.
struct Fq12Config
{
    using BaseFieldT = Fq;
    using ValueT = Fq6;

    static constexpr uint8_t DEGREE = 2;
};
using Fq12 = ecc::ExtFieldElem<Fq12Config>;

/// Multiplies two Fq^2 field elements
constexpr Fq2 multiply(const Fq2& a, const Fq2& b) noexcept
{
    const auto& [a0, a1] = a.coeffs;
    const auto& [b0, b1] = b.coeffs;
    return Fq2({a0 * b0 - a1 * b1, a1 * b0 + a0 * b1});
}

/// Squares an Fq^2 field element.
constexpr Fq2 sqr(const Fq2& a) noexcept
{
    const auto& [a0, a1] = a.coeffs;

    // (a0 + a1*u)^2 = (a0+a1)*(a0-a1) + 2a0a1*u.
    const auto a0a1 = a0 * a1;
    return Fq2({(a0 + a1) * (a0 - a1), a0a1 + a0a1});
}

/// Multiplies two Fq^6 field elements
constexpr Fq6 multiply(const Fq6& a, const Fq6& b) noexcept
{
    const auto& [a0, a1, a2] = a.coeffs;
    const auto& [b0, b1, b2] = b.coeffs;

    const Fq2& ksi = Fq6Config::ksi;

    const auto t0 = a0 * b0;
    const auto t1 = a1 * b1;
    const auto t2 = a2 * b2;

    const auto c0 = ((a1 + a2) * (b1 + b2) - t1 - t2) * ksi + t0;
    const auto c1 = (a0 + a1) * (b0 + b1) - t0 - t1 + ksi * t2;
    const auto c2 = (a0 + a2) * (b0 + b2) - t0 - t2 + t1;

    return Fq6({c0, c1, c2});
}

/// Multiplies two Fq^12 field elements
constexpr Fq12 multiply(const Fq12& a, const Fq12& b) noexcept
{
    const auto& [a0, a1] = a.coeffs;
    const auto& [b0, b1] = b.coeffs;

    const auto t0 = a0 * b0;
    const auto t1 = a1 * b1;

    const Fq2& ksi = Fq6Config::ksi;

    const auto c0 = t0 + Fq6({ksi * t1.coeffs[2], t1.coeffs[0], t1.coeffs[1]});  // gamma is sparse.
    const auto c1 = (a0 + a1) * (b0 + b1) - t0 - t1;

    return Fq12({c0, c1});
}

/// Inverses the Fq^2 field element
inline Fq2 inverse(const Fq2& f) noexcept
{
    const auto& [a0, a1] = f.coeffs;

    auto t0 = a0 * a0;
    auto t1 = a1 * a1;

    t0 = t0 + t1;
    t1 = t0.inv();

    const auto c0 = a0 * t1;
    const auto c1 = -(a1 * t1);

    return Fq2({c0, c1});
}

/// Inverses the Fq^6 field element
inline Fq6 inverse(const Fq6& f) noexcept
{
    const auto& [a0, a1, a2] = f.coeffs;

    const Fq2& ksi = Fq6Config::ksi;

    const auto t0 = a0 * a0;
    const auto t1 = a1 * a1;
    const auto t2 = a2 * a2;

    const auto t3 = a0 * a1;
    const auto t4 = a0 * a2;
    const auto t5 = a2 * a1;

    const auto c0 = t0 - ksi * t5;
    const auto c1 = ksi * t2 - t3;
    const auto c2 = t1 - t4;

    const auto t = a0 * c0 + (a2 * c1 + a1 * c2) * ksi;
    const auto t6 = t.inv();

    return Fq6({c0 * t6, c1 * t6, c2 * t6});
}

/// Inverses the Fq^12 field element
inline Fq12 inverse(const Fq12& f) noexcept
{
    const auto& [a0, a1] = f.coeffs;

    auto t0 = a0 * a0;
    auto t1 = a1 * a1;

    const Fq2& ksi = Fq6Config::ksi;

    t0 = t0 - Fq6({ksi * t1.coeffs[2], t1.coeffs[0], t1.coeffs[1]});  // gamma is sparse.
    t1 = t0.inv();

    const auto c0 = a0 * t1;
    const auto c1 = -(a1 * t1);

    return Fq12({c0, c1});
}
}  // namespace evmone::crypto::bn254
