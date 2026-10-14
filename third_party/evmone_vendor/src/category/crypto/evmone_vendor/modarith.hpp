// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <intx/intx.hpp>
#include <cassert>

namespace evmone::crypto
{
/// Computes the modular inverse of a modulo 2³², satisfying a⋅inv = 1 mod 2³².
/// Only odd arguments are invertible modulo a power of two.
constexpr uint32_t modinv_pow2(uint32_t a) noexcept
{
    assert(a % 2 == 1);  // The argument must be odd, otherwise the inverse does not exist.

    // Start with inversion mod 2⁴, which is a³ mod 2⁴ (for odd a).
    // All 8 cases can be verified manually, but the formal explanation can be found in:
    // https://en.wikipedia.org/wiki/Multiplicative_group_of_integers_modulo_n#Powers_of_2.
    // This is better tradeoff than a mod 2² plus one Newton-Raphson iteration.
    // We also avoid explicit mod 2⁴ because the top garbage bits are fine.
    auto inv = a * a * a;

    // Use the Newton–Raphson numeric method, see e.g.
    // https://gmplib.org/~tege/divcnst-pldi94.pdf#page=9, formula (9.2)
    // Each iteration doubles the number of correct bits, starting from 4:
    // 8, 16, 32, ..., so for 32-bit value we need 3 iterations.
    // TODO(C++23): static
    constexpr auto ITERATIONS = std::countr_zero(sizeof(a) * 8 / 4);
    for (auto i = 0; i < ITERATIONS; ++i)
        inv *= 2 - a * inv;  // Overflows are fine because they wrap around modulo 2³².

    assert(inv * a == 1);  // Verify the result.
    return inv;
}

/// Computes the modular inverse of a modulo 2⁶⁴, satisfying a⋅inv = 1 mod 2⁶⁴.
/// Only odd arguments are invertible modulo a power of two.
constexpr uint64_t modinv_pow2(uint64_t a) noexcept
{
    assert(a % 2 == 1);  // The argument must be odd, otherwise the inverse does not exist.
    uint64_t inv = modinv_pow2(static_cast<uint32_t>(a));  // Start with inversion mod 2³².
    inv *= 2 - a * inv;    // One Newton-Raphson iteration: 64 bits correct.
    assert(inv * a == 1);  // Verify the result.
    return inv;
}

/// Compute the modulus inverse for Montgomery multiplication, i.e., N': mod⋅N' = 2⁶⁴-1.
template <typename UintT>
constexpr uint64_t compute_mont_mod_inv(const UintT& mod) noexcept
{
    // Compute the inversion mod[0]⁻¹ mod 2⁶⁴, then the final result is N' = -mod[0]⁻¹
    // because this gives mod⋅N' = -1 mod 2⁶⁴ = 2⁶⁴-1.
    return -modinv_pow2(mod[0]);
}

constexpr std::pair<uint64_t, uint64_t> addmul(
    uint64_t t, uint64_t a, uint64_t b, uint64_t c) noexcept
{
    const auto p = intx::umul(a, b) + t + c;
    return {p[1], p[0]};
}

/// Performs a modular addition. Requires x < mod and y < mod.
template <typename UintT>
constexpr UintT modadd(const UintT& x, const UintT& y, const UintT& mod) noexcept
{
    assert(x < mod);
    assert(y < mod);
    const auto s = addc(x, y);  // TODO: cannot overflow if modulus is sparse (e.g. 255 bits).
    const auto d = subc(s.value, mod);
    return (!s.carry && d.carry) ? s.value : d.value;
}

/// Performs a modular subtraction. Requires x < mod and y < mod.
template <typename UintT>
constexpr UintT modsub(const UintT& x, const UintT& y, const UintT& mod) noexcept
{
    assert(x < mod);
    assert(y < mod);
    const auto d = subc(x, y);
    const auto s = d.value + mod;
    return (d.carry) ? s : d.value;
}

/// Computes scale⋅x⁻¹ % mod, i.e. the modular inverse of x scaled by the given factor.
/// Returns 0 for non-invertible x (including x == 0).
/// Requires an odd mod not less than 3, and both x and scale less than mod.
///
/// The scale is the initial value of the Bézout coefficient u and the algorithm is linear in it,
/// so any factor can be folded into the result for free.
template <typename UintT>
constexpr UintT modinv_scaled(const UintT& x, const UintT& scale, const UintT& mod) noexcept
{
    assert((mod & 1) == 1);
    assert(mod >= 3);
    assert(x < mod);
    assert(scale < mod);  // Otherwise the first modsub() below gets a non-reduced operand.

    // Precompute inverse of 2 modulo mod: inv2 * 2 % mod == 1.
    // The 1/2 is inexact division that can be fixed by adding "0" to the numerator
    // and making it even: (mod + 1) / 2. To avoid potential overflow of (1 + mod)
    // we rewrite it further to (mod - 1 + 2) / 2 = (mod - 1) / 2 + 1 = ⌊mod / 2⌋ + 1.
    const auto inv2 = (mod >> 1) + 1;

    // Use extended binary Euclidean algorithm. This evolves variables a and b until a is 0.
    // Then GCD(x, mod) is in b. If GCD(x, mod) == 1 then the inversion exists and is in v.
    // This follows the classic algorithm (Algorithm 1) presented in
    // "Optimized Binary GCD for Modular Inversion".
    // https://eprint.iacr.org/2020/972.pdf#algorithm.1
    // TODO: The same paper has additional optimizations that could be applied.
    UintT a = x;
    UintT b = mod;
    UintT u = scale;
    UintT v = 0;

    while (a != 0)
    {
        if ((a & 1) != 0)
        {
            // if a is odd, update it to a - b.
            if (const auto [d, less] = subc(a, b); less)
            {
                // swap a and b in case a < b.
                b = a;
                a = -d;

                using namespace std;
                swap(u, v);
            }
            else
            {
                a = d;
            }
            u = modsub(u, v, mod);
        }

        // Compute a / 2 % mod, a is even so division is exact and can be computed as ⌊a / 2⌋.
        a >>= 1;

        // Compute u / 2 % mod. If u is even, this can be computed as ⌊u / 2⌋.
        // Otherwise, (u - 1 + 1) / 2 = ⌊u / 2⌋ + (1 / 2 % mod).
        const auto u_odd = (u & 1) != 0;
        u >>= 1;
        if (u_odd)
            u += inv2;  // if u is odd, add back ½ % mod.
    }

    if (b != 1) [[unlikely]]
        v = 0;  // not invertible
    return v;
}

/// The modular arithmetic operations using the Montgomery form of the values.
template <typename UintT>
class ModArith
{
    const UintT mod_;  ///< The modulus.

    const UintT r_squared_;  ///< R² % mod.

    /// The modulus inversion, i.e. the number N' such that mod⋅N' = 2⁶⁴-1.
    const uint64_t mod_inv_;

    /// Compute R² % mod.
    static constexpr UintT compute_r_squared(const UintT& mod) noexcept
    {
        // R is 2^num_bits, R² is 2^(2*num_bits) and needs 2*num_bits+1 bits to represent,
        // rounded to 2*num_bits+64 for intx requirements.
        constexpr auto RR = intx::uint<UintT::num_bits * 2 + 64>{1} << (UintT::num_bits * 2);
        return intx::udivrem(RR, mod).rem;
    }

public:
    constexpr explicit ModArith(const UintT& mod) noexcept
      : mod_{mod}, r_squared_{compute_r_squared(mod)}, mod_inv_{compute_mont_mod_inv(mod)}
    {}

    /// Returns the modulus.
    constexpr const UintT& mod() const noexcept { return mod_; }

    /// Converts a value to Montgomery form.
    ///
    /// This is done by using Montgomery multiplication mul(x, R²)
    /// what gives aR²R⁻¹ % mod = aR % mod.
    constexpr UintT to_mont(const UintT& x) const noexcept { return mul(x, r_squared_); }

    /// Converts a value in Montgomery form back to normal value.
    ///
    /// Given the x is the Montgomery form x = aR, the conversion is done by using
    /// Montgomery multiplication mul(x, 1) what gives aRR⁻¹ % mod = a % mod.
    constexpr UintT from_mont(const UintT& x) const noexcept { return mul(x, 1); }

    /// Performs a Montgomery modular multiplication.
    ///
    /// Inputs must be in Montgomery form: x = aR, y = bR.
    /// This computes Montgomery multiplication xyR⁻¹ % mod what gives aRbRR⁻¹ % mod = abR % mod.
    /// The result (abR) is in Montgomery form.
    constexpr UintT mul(const UintT& x, const UintT& y) const noexcept
    {
        // Coarsely Integrated Operand Scanning (CIOS) Method
        // Based on 2.3.2 from
        // High-Speed Algorithms & Architectures For Number-Theoretic Cryptosystems
        // https://www.microsoft.com/en-us/research/wp-content/uploads/1998/06/97Acar.pdf

        constexpr auto S = UintT::num_words;  // TODO(C++23): Make it static

        intx::uint<UintT::num_bits + 64> t;
        for (size_t i = 0; i != S; ++i)
        {
            uint64_t c = 0;
#pragma GCC unroll 8
            for (size_t j = 0; j != S; ++j)
                std::tie(c, t[j]) = addmul(t[j], x[j], y[i], c);
            auto tmp = intx::addc(t[S], c);
            t[S] = tmp.value;
            const auto d = tmp.carry;  // TODO: Carry is 0 for sparse modulus.

            const auto m = t[0] * mod_inv_;
            std::tie(c, std::ignore) = addmul(t[0], m, mod_[0], 0);
#pragma GCC unroll 8
            for (size_t j = 1; j != S; ++j)
                std::tie(c, t[j - 1]) = addmul(t[j], m, mod_[j], c);
            tmp = intx::addc(t[S], c);
            t[S - 1] = tmp.value;
            t[S] = d + tmp.carry;  // TODO: Carry is 0 for sparse modulus.
        }

        if (t >= mod_)
            t -= mod_;

        return static_cast<UintT>(t);
    }

    /// Performs a modular addition.
    constexpr UintT add(const UintT& x, const UintT& y) const noexcept
    {
        // Using generic procedure is fine for Montgomery forms.
        return modadd(x, y, mod_);
    }

    /// Performs a modular subtraction.
    constexpr UintT sub(const UintT& x, const UintT& y) const noexcept
    {
        // Using generic procedure is fine for Montgomery forms.
        return modsub(x, y, mod_);
    }

    /// Computes modular inverse of x in Montgomery form. Result is in Montgomery form.
    /// Returns 0 for non-invertible x (including x == 0).
    constexpr UintT inv(const UintT& x) const noexcept
    {
        // The input XR would invert to X⁻¹R⁻¹, so scaling by R² gives the expected Montgomery
        // form X⁻¹R at no extra cost.
        return modinv_scaled(x, r_squared_, mod_);
    }
};
}  // namespace evmone::crypto
