// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include "modarith.hpp"
#include <optional>
#include <span>

namespace evmone::crypto::ecc
{
template <int N>
struct Constant : std::integral_constant<int, N>
{
    consteval explicit(false) Constant(int v) noexcept
    {
        if (N != v)
            intx::unreachable();
    }
};
using zero_t = Constant<0>;
using one_t = Constant<1>;

/// The order specification (prime number) for a finite field.
template <typename T>
concept FieldSpec = requires { T::ORDER; };

/// A representation of an element in a prime field.
template <FieldSpec Spec>
class FieldElement
{
    using uint_type = std::remove_const_t<decltype(Spec::ORDER)>;
    static constexpr ModArith<uint_type> Fp{Spec::ORDER};

    uint_type value_;

    /// Wraps a value into the Element type assuming it is already in the internal ModArith form.
    [[gnu::always_inline]] static constexpr FieldElement wrap(const uint_type& v) noexcept
    {
        FieldElement element;
        element.value_ = v;
        return element;
    }

public:
    /// The alias to the finite field's order.
    static constexpr auto& ORDER = Spec::ORDER;

    FieldElement() = default;

    constexpr explicit FieldElement(uint_type v) : value_{Fp.to_mont(v)} {}

    constexpr uint_type value() const noexcept { return Fp.from_mont(value_); }

    /// The valid range for from_bytes().
    enum class Range : bool
    {
        full,  ///< Valid in [0, ORDER).
        half,  ///< Valid in [0, ORDER/2].
    };

    template <Range R = Range::full>
    static constexpr std::optional<FieldElement> from_bytes(
        std::span<const uint8_t, sizeof(uint_type)> b) noexcept
    {
        constexpr auto LIMIT = R == Range::full ? ORDER : ORDER / 2 + 1;

        const auto x = intx::be::load<uint_type>(b);
        if (x >= LIMIT) [[unlikely]]
            return std::nullopt;
        return FieldElement{x};
    }

    constexpr void to_bytes(std::span<uint8_t, sizeof(uint_type)> b) const noexcept
    {
        intx::be::store(b, value());
    }


    constexpr explicit operator bool() const noexcept { return static_cast<bool>(value_); }

    friend constexpr bool operator==(const FieldElement&, const FieldElement&) = default;

    friend constexpr bool operator==(const FieldElement& a, zero_t) noexcept { return !a.value_; }

    friend constexpr auto operator*(const FieldElement& a, const FieldElement& b) noexcept
    {
        return wrap(Fp.mul(a.value_, b.value_));
    }

    friend constexpr auto operator+(const FieldElement& a, const FieldElement& b) noexcept
    {
        return wrap(Fp.add(a.value_, b.value_));
    }

    FieldElement& operator+=(const FieldElement& b) noexcept
    {
        value_ = Fp.add(value_, b.value_);
        return *this;
    }

    friend constexpr auto operator-(const FieldElement& a, const FieldElement& b) noexcept
    {
        return wrap(Fp.sub(a.value_, b.value_));
    }

    friend constexpr auto operator-(const FieldElement& a) noexcept
    {
        return wrap(Fp.sub(0, a.value_));
    }

    /// Division returns 0 when the divisor is 0. See ModArith::inv().
    friend constexpr auto operator/(one_t, const FieldElement& a) noexcept
    {
        return wrap(Fp.inv(a.value_));
    }

    /// Division returns 0 when the divisor is 0. See ModArith::inv().
    friend constexpr auto operator/(const FieldElement& a, const FieldElement& b) noexcept
    {
        return wrap(Fp.mul(a.value_, Fp.inv(b.value_)));
    }

    /// Named 1/x inversion method. Needed in the pairing templates.
    /// Returns 0 when this element is 0. See ModArith::inv().
    constexpr auto inv() const noexcept { return wrap(Fp.inv(value_)); }

    /// Named one element. Needed in the pairing templates.
    static constexpr auto one() noexcept { return FieldElement{1}; }
};

/// The affine (two coordinates) point on an Elliptic Curve over a prime field.
template <typename Curve>
struct AffinePoint
{
    using FE = Curve::Fp;

    FE x;
    FE y;

    AffinePoint() = default;
    constexpr AffinePoint(const FE& x_, const FE& y_) noexcept : x{x_}, y{y_} {}

    /// Create the point from literal values. Only available when Curve defines uint_type.
    template <typename C = Curve>
        requires requires { typename C::uint_type; }
    consteval AffinePoint(
        const typename C::uint_type& x_value, const typename C::uint_type& y_value) noexcept
      : x{x_value}, y{y_value}
    {}

    friend constexpr bool operator==(const AffinePoint&, const AffinePoint&) = default;

    friend constexpr bool operator==(const AffinePoint& p, zero_t) noexcept
    {
        return p == AffinePoint{};
    }

    friend constexpr AffinePoint operator-(const AffinePoint& p) noexcept { return {p.x, -p.y}; }

    static constexpr std::optional<AffinePoint> from_bytes(
        std::span<const uint8_t, sizeof(FE) * 2> b) noexcept
    {
        const auto x = FE::from_bytes(b.template subspan<0, sizeof(FE)>());
        const auto y = FE::from_bytes(b.template subspan<sizeof(FE), sizeof(FE)>());
        if (!x.has_value() || !y.has_value()) [[unlikely]]
            return std::nullopt;
        return AffinePoint{*x, *y};
    }

    constexpr void to_bytes(std::span<uint8_t, sizeof(FE) * 2> b) const noexcept
    {
        x.to_bytes(b.template subspan<0, sizeof(FE)>());
        y.to_bytes(b.template subspan<sizeof(FE), sizeof(FE)>());
    }
};

/// Elliptic curve point in Jacobian coordinates (X, Y, Z)
/// representing the affine point (X/Z², Y/Z³).
template <typename Curve>
struct ProjPoint
{
    using FE = Curve::Fp;
    FE x;
    FE y = FE::one();
    FE z;

    ProjPoint() = default;
    constexpr ProjPoint(const FE& x_, const FE& y_, const FE& z_) noexcept : x{x_}, y{y_}, z{z_} {}
    constexpr explicit ProjPoint(const AffinePoint<Curve>& p) noexcept
      : x{p.x}, y{p.y}, z{FE::one()}
    {}

    friend constexpr bool operator==(const ProjPoint& p, zero_t) noexcept { return p.z == 0; }

    friend constexpr bool operator==(const ProjPoint& p, const ProjPoint& q) noexcept
    {
        const auto& [x1, y1, z1] = p;
        const auto& [x2, y2, z2] = q;
        const auto z1z1 = z1 * z1;
        const auto z1z1z1 = z1z1 * z1;
        const auto z2z2 = z2 * z2;
        const auto z2z2z2 = z2z2 * z2;
        return x1 * z2z2 == x2 * z1z1 && y1 * z2z2z2 == y2 * z1z1z1;
    }

    friend constexpr ProjPoint operator-(const ProjPoint& p) noexcept { return {p.x, -p.y, p.z}; }
};

/// Converts a projected point to an affine point.
template <typename Curve>
AffinePoint<Curve> to_affine(const ProjPoint<Curve>& p) noexcept
{
    // This works correctly for the point at infinity (z == 0) because then z_inv == 0.
    const auto z_inv = 1 / p.z;
    const auto zz_inv = z_inv * z_inv;
    const auto zzz_inv = zz_inv * z_inv;
    return {p.x * zz_inv, p.y * zzz_inv};
}

/// Elliptic curve point addition in affine coordinates.
///
/// Computes P ⊕ Q for two points in affine coordinates on the elliptic curve.
/// This procedure handles all inputs (e.g. doubling or points at infinity).
/// The produced result is also in affine coordinates. Therefore, this is useful only for one-off
/// additions, as otherwise multiple additions would be inefficient due to repeated inversions.
template <typename Curve>
AffinePoint<Curve> add_affine(const AffinePoint<Curve>& p, const AffinePoint<Curve>& q) noexcept
{
    if (p == 0)
        return q;
    if (q == 0)
        return p;

    const auto& [x1, y1] = p;
    const auto& [x2, y2] = q;

    // Use classic formula for point addition.
    // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#Point_operations

    auto dx = x2 - x1;
    auto dy = y2 - y1;
    if (dx == 0)
    {
        if (dy != 0)    // For opposite points
            return {};  // return the point at infinity.

        // For coincident points find the slope of the tangent line.
        const auto xx = x1 * x1;
        dy = xx + xx + xx;
        if constexpr (Curve::A != 0)
            dy += typename Curve::Fp{Curve::A};
        dx = y1 + y1;
        assert(dx != 0);  // 2-torsion (y=0): unreachable for prime-order curves.
    }
    const auto slope = dy / dx;

    const auto xr = slope * slope - x1 - x2;
    const auto yr = slope * (x1 - xr) - y1;
    return {xr, yr};
}

/// Elliptic curve point addition in Jacobian coordinates.
///
/// Computes P ⊕ Q for two points in Jacobian coordinates on the elliptic curve.
/// This procedure handles all inputs (e.g. doubling or points at infinity).
template <typename Curve>
ProjPoint<Curve> add(const ProjPoint<Curve>& p, const ProjPoint<Curve>& q) noexcept
{
    if (p == 0)
        return q;
    if (q == 0)
        // TODO: Untested and untestable via precompile call (for secp256k1 and secp256r1).
        return p;

    // Use the "add-1998-cmo-2" formula for curve in Jacobian coordinates.
    // The cost is 12M + 4S + 6add + 1*2.
    // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-1998-cmo-2
    // TODO: The newer formula "add-2007-bl" trades one multiplication for one squaring and
    //   additional additions. We don't have dedicated squaring operation yet, so it's not clear
    //   if it would be faster.

    const auto& [x1, y1, z1] = p;
    const auto& [x2, y2, z2] = q;

    const auto z1z1 = z1 * z1;
    const auto z2z2 = z2 * z2;
    const auto u1 = x1 * z2z2;
    const auto u2 = x2 * z1z1;
    const auto z1z1z1 = z1 * z1z1;
    const auto z2z2z2 = z2 * z2z2;
    const auto s1 = y1 * z2z2z2;
    const auto s2 = y2 * z1z1z1;
    const auto h = u2 - u1;
    const auto r = s2 - s1;

    // Handle point doubling in case p == q, i.e. when u1 == u2 and s1 == s2.
    // TODO: Untested case of two points having the same y coordinate but different x.
    //       The following assertion (r == 0) => (h == 0) should fail in that case.
    assert(r != 0 || h == 0);
    if (h == 0 && r == 0) [[unlikely]]
        return dbl(p);

    const auto hh = h * h;
    const auto hhh = h * hh;
    const auto v = u1 * hh;
    const auto t2 = r * r;
    const auto t3 = v + v;
    const auto t4 = t2 - hhh;
    const auto x3 = t4 - t3;
    const auto t5 = v - x3;
    const auto t6 = s1 * hhh;
    const auto t7 = r * t5;
    const auto y3 = t7 - t6;
    const auto t8 = z2 * h;
    const auto z3 = z1 * t8;

    return {x3, y3, z3};
}

/// Mixed addition of elliptic curve points.
///
/// Computes P ⊕ Q for a point P in Jacobian coordinates and a point Q in affine coordinates.
/// This procedure handles all inputs (e.g. doubling or points at infinity).
template <typename Curve>
ProjPoint<Curve> add(const ProjPoint<Curve>& p, const AffinePoint<Curve>& q) noexcept
{
    if (q == 0)
        // TODO: Untested and untestable via precompile call (for secp256r1).
        return p;
    if (p == 0)
        return ProjPoint(q);

    // Use the "madd" formula for curve in Jacobian coordinates.
    // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-madd
    // Modified to properly support adding the same point.

    const auto& [x1, y1, z1] = p;
    const auto& [x2, y2] = q;

    const auto z1z1 = z1 * z1;
    const auto u2 = x2 * z1z1;
    const auto z1z1z1 = z1 * z1z1;
    const auto s2 = y2 * z1z1z1;
    const auto h = u2 - x1;
    const auto t1 = h + h;
    const auto i = t1 * t1;
    const auto j = h * i;
    const auto t2 = s2 - y1;

    // Handle point doubling in case p == q.
    // p == q (in jacobian coordinates) if and only if x1 == x2 * z1z1 and y1 = y2 * z1z1z1
    if (h == 0 && t2 == 0) [[unlikely]]
        return dbl(p);

    const auto r = t2 + t2;
    const auto v = x1 * i;
    const auto t3 = r * r;
    const auto t4 = v + v;
    const auto t5 = t3 - j;
    const auto x3 = t5 - t4;
    const auto t6 = v - x3;
    const auto t7 = y1 * j;
    const auto t8 = t7 + t7;
    const auto t9 = r * t6;
    const auto y3 = t9 - t8;
    const auto t10 = z1 * h;
    const auto z3 = t10 + t10;

    return {x3, y3, z3};
}

template <typename Curve>
constexpr ProjPoint<Curve> dbl(const ProjPoint<Curve>& p) noexcept
{
    const auto& [x1, y1, z1] = p;

    if constexpr (Curve::A == 0)
    {
        // Use the "dbl-2009-l" formula for a=0 curve in Jacobian coordinates.
        // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l

        const auto xx = x1 * x1;
        const auto yy = y1 * y1;
        const auto yyyy = yy * yy;
        const auto t0 = x1 + yy;
        const auto t1 = t0 * t0;
        const auto t2 = t1 - xx;
        const auto t3 = t2 - yyyy;
        const auto d = t3 + t3;
        const auto e = xx + xx + xx;
        const auto f = e * e;
        const auto t4 = d + d;
        const auto x3 = f - t4;
        const auto t6 = d - x3;
        const auto yyyy2 = yyyy + yyyy;
        const auto yyyy4 = yyyy2 + yyyy2;
        const auto yyyy8 = yyyy4 + yyyy4;
        const auto t9 = e * t6;
        const auto y3 = t9 - yyyy8;
        const auto t10 = y1 * z1;
        const auto z3 = t10 + t10;
        return {x3, y3, z3};
    }
    else if constexpr (Curve::A == Curve::FIELD_PRIME - 3)
    {
        // Use the "dbl-2001-b" doubling formula.
        // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b

        const auto zz = z1 * z1;
        const auto yy = y1 * y1;
        const auto xyy = x1 * yy;
        const auto t0 = x1 - zz;
        const auto t1 = x1 + zz;
        const auto t2 = t0 * t1;
        const auto alpha = t2 + t2 + t2;
        const auto t3 = alpha * alpha;
        const auto xyy2 = xyy + xyy;
        const auto xyy4 = xyy2 + xyy2;
        const auto xyy8 = xyy4 + xyy4;
        const auto x3 = t3 - xyy8;
        const auto t5 = y1 + z1;
        const auto t6 = t5 * t5;
        const auto t7 = t6 - yy;
        const auto z3 = t7 - zz;
        const auto t9 = xyy4 - x3;
        const auto yyyy = yy * yy;
        const auto yyyy2 = yyyy + yyyy;
        const auto yyyy4 = yyyy2 + yyyy2;
        const auto yyyy8 = yyyy4 + yyyy4;
        const auto t12 = alpha * t9;
        const auto y3 = t12 - yyyy8;
        return {x3, y3, z3};
    }
    else
    {
        // TODO(c++23): Use fake always-false condition for older compilers.
        static_assert(Curve::A == 0, "unsupported Curve::A value");
    }
}

/// Computes scalar multiplication [c]P.
/// Not constant-time: execution time depends on the scalar value.
/// Safe for EVM precompiles (public calldata), not for secret key operations.
template <typename Curve>
ProjPoint<Curve> mul(const AffinePoint<Curve>& p, typename Curve::uint_type c) noexcept
{
    // Reduce the scalar by the curve group order.
    // This allows using more efficient add algorithm in the loop because doubling cannot happen.
    while (true)
    {
        const auto [reduced_c, less_than] = subc(c, Curve::ORDER);
        if (less_than) [[likely]]
            break;
        // TODO: Untested and untestable via precompile call (for secp256r1).
        c = reduced_c;
    }

    ProjPoint<Curve> r;
    for (size_t i = bit_width(c); i != 0; --i)
    {
        r = ecc::dbl(r);
        if (bit_test(c, i - 1))
            r = ecc::add(r, p);
    }
    return r;
}

/// Computes multi-scalar multiplication of u×P ⊕ v×Q.
///
/// Not constant-time. See mul() for details.
/// The implementation uses the "Straus-Shamir trick": https://eprint.iacr.org/2003/257.pdf#page=7.
template <typename Curve>
ProjPoint<Curve> msm(const typename Curve::uint_type& u, const AffinePoint<Curve>& p,
    const typename Curve::uint_type& v, const AffinePoint<Curve>& q)
{
    ProjPoint<Curve> r;

    const auto bit_width = intx::bit_width(u | v);
    if (bit_width == 0)
        return r;

    // Precompute affine P + Q. Works correctly if P == Q.
    const auto h = add_affine(p, q);

    // Create lookup table for points. The index 0 is unused.
    // TODO: Put 0 at index 0 and use it in the loop to avoid the branch.
    const AffinePoint<Curve>* const points[]{nullptr, &p, &q, &h};

    for (auto i = bit_width; i != 0; --i)
    {
        r = dbl(r);

        const auto u_bit = bit_test(u, i - 1);
        const auto v_bit = bit_test(v, i - 1);
        const auto idx = 2 * size_t{v_bit} + size_t{u_bit};
        if (idx == 0)
            continue;
        r = add(r, *points[idx]);
    }

    return r;
}

template <typename UIntT>
struct SignedScalar
{
    bool sign = false;  // The sign of the scalar: false = positive, true = negative.
    UIntT value;
};


/// Verifies k ≡ k₁ + k₂·λ (mod N) and checks that k₁ and k₂ are "short" scalars.
template <typename Curve>
[[maybe_unused, nodiscard]] bool verify_scalar_decomposition(const typename Curve::uint_type& k,
    const SignedScalar<typename Curve::uint_type>& k1,
    const SignedScalar<typename Curve::uint_type>& k2) noexcept
{
    // Verify k ≡ k₁ + k₂·λ (mod N).
    {
        static constexpr ModArith N{Curve::ORDER};
        auto r_k1 = N.to_mont(k1.value);
        if (k1.sign)
            r_k1 = N.sub(0, r_k1);
        auto r_k2 = N.to_mont(k2.value);
        if (k2.sign)
            r_k2 = N.sub(0, r_k2);

        const auto r_k = N.to_mont(k);

        const auto right = N.add(r_k1, N.mul(r_k2, N.to_mont(Curve::LAMBDA)));
        if (r_k != right)
            return false;
    }

    // Verify for u = (k₁, k₂) that ‖u‖ <= max(‖v₁‖, ‖v₂‖).
    {
        static constexpr auto V1_NORM_SQUARED =
            Curve::X1 * Curve::X1 + Curve::MINUS_Y1 * Curve::MINUS_Y1;
        static constexpr auto V2_NORM_SQUARED = Curve::X2 * Curve::X2 + Curve::Y2 * Curve::Y2;
        static constexpr auto MAX_NORM_SQUARED = std::max(V1_NORM_SQUARED, V2_NORM_SQUARED);
        const auto u_norm_squared = k1.value * k1.value + k2.value * k2.value;
        return u_norm_squared <= MAX_NORM_SQUARED;
    }
}

/// Decomposes a scalar k into "short" scalars k₁ and k₂ such that k₁ + k₂·λ ≡ k (mod N).
///
/// This decomposition allows more efficient scalar multiplication by using the multi-scalar
/// multiplication (MSM) and the GLV endomorphism.
/// The endomorphism ϕ: E → E defined as (x,y) → (βx,y) with eigenvalue λ allows computing
/// [λ](x,y) = (βx,y) with only one multiplication in 𝔽ₚ instead of a full scalar multiplication.
///
/// Moreover, to compute the short scalars k₁ and k₂, we need linearly independent short vectors
/// (v₁=(x₁,y₁), v₂=(x₂,y₂)) such that f(v₁) = f(v₂) = 0,
/// where f: ℤ×ℤ → ℤₙ is defined as (x,y) → (x + y·λ), where λ² + λ ≡ -1 mod N.
///
/// See https://www.iacr.org/archive/crypto2001/21390189.pdf for details.
///
/// The Curve type must provide the endomorphism parameters: LAMBDA, BETA, X1, MINUS_Y1, X2, Y2.
template <typename Curve>
std::array<SignedScalar<typename Curve::uint_type>, 2> decompose(
    const typename Curve::uint_type& k) noexcept
{
    using UIntT = Curve::uint_type;

    // Validate the provided setup parameters.
    // λ² + λ ≡ -1 mod n
    static_assert((umul(Curve::LAMBDA, Curve::LAMBDA) + Curve::LAMBDA + 1) % Curve::ORDER == 0);
    // f: (x, y) → (x + λy) mod N
    // f(v₁) = 0
    static_assert(
        (Curve::X1 + umul(Curve::ORDER - Curve::MINUS_Y1, Curve::LAMBDA)) % Curve::ORDER == 0);
    // f(v₂) = 0
    static_assert((Curve::X2 + umul(Curve::Y2, Curve::LAMBDA)) % Curve::ORDER == 0);

    static constexpr auto round_div = [](const auto& a) noexcept {
        // DET is the (v₁, v₂) matrix determinant.
        static constexpr auto WIDE_DET =
            umul(Curve::X1, Curve::Y2) + umul(Curve::X2, Curve::MINUS_Y1);
        static_assert(WIDE_DET <= std::numeric_limits<UIntT>::max());
        static constexpr auto DET = static_cast<UIntT>(WIDE_DET);
        static constexpr auto HALF_DET = DET / 2;

        const auto [wide_q, r] = udivrem(a, DET);
        // Division reduces the quotient enough to fit into a single uint.
        // This can be shown at compile-time by inspecting the DET and Y2/-Y1 values.
        assert(wide_q < std::numeric_limits<UIntT>::max());
        const auto q = static_cast<UIntT>(wide_q);
        return q + (r > HALF_DET);  // Round to nearest.
    };

    // Solve a system of two equations using Cramer method.
    // ⎡X1 X2⎤ * ⎡b1⎤ = ⎡k⎤
    // ⎣Y1 Y2⎦   ⎣b2⎦   ⎣0⎦
    // and then approximate to the nearest integers:
    // b1 = ⌊ Y2·k ÷ DET⌉
    // b2 = ⌊-Y1·k ÷ DET⌉
    const auto b1 = round_div(umul(k, Curve::Y2));
    const auto b2 = round_div(umul(k, Curve::MINUS_Y1));

    // k1 = k - (x1*b1 + x2*b2)
    const auto x1b1_x2b2 = umul(b1, Curve::X1) + umul(b2, Curve::X2);
    const auto [wide_k1, k1_is_neg] = subc(decltype(x1b1_x2b2){k}, x1b1_x2b2);
    const auto k1_abs = k1_is_neg ? -static_cast<UIntT>(wide_k1) : static_cast<UIntT>(wide_k1);

    // k2 = 0 - (y1*b1 + y2*b2)
    const auto [wide_k2, k2_is_neg] = subc(umul(b1, Curve::MINUS_Y1), umul(b2, Curve::Y2));
    const auto k2_abs = k2_is_neg ? -static_cast<UIntT>(wide_k2) : static_cast<UIntT>(wide_k2);

    const SignedScalar k1{k1_is_neg, k1_abs};
    const SignedScalar k2{k2_is_neg, k2_abs};
    assert(verify_scalar_decomposition<Curve>(k, k1, k2));
    return {k1, k2};
}

}  // namespace evmone::crypto::ecc
