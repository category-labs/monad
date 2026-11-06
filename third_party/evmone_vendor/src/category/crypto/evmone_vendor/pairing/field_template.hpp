// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2024 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <array>
#include <concepts>
#include <type_traits>

namespace evmone::crypto::ecc
{
/// Implements extension field over the base field or other extension fields.
/// It is a template struct which can be reused for different pairing implementations.
template <typename ConfigT>
struct ExtFieldElem
{
    using ValueT = ConfigT::ValueT;
    using Base = ConfigT::BaseFieldT;
    static constexpr auto DEGREE = ConfigT::DEGREE;
    using CoeffArrT = std::array<ValueT, DEGREE>;

    // TODO: Add operator[] for nicer access.
    CoeffArrT coeffs = {};

    constexpr ExtFieldElem() noexcept = default;

    /// Create an element from an array of coefficients.
    /// TODO: This constructor may be optimized to avoid copying the array.
    explicit constexpr ExtFieldElem(const CoeffArrT& cs) noexcept : coeffs{cs} {}

    /// Create an element from literal coefficient values, converted to the underlying
    /// representation at compile-time. Allows defining constants as e.g. Fq2{1, 2}.
    template <typename... Ts>
        requires(sizeof...(Ts) == DEGREE && (std::constructible_from<ValueT, Ts> && ...) &&
                 (!std::same_as<std::remove_cvref_t<Ts>, ValueT> && ...))
    consteval ExtFieldElem(const Ts&... cs) noexcept : coeffs{ValueT{cs}...}
    {}

    /// Returns the conjugate of a degree-2 extension field element: (a, b) → (a, -b).
    constexpr ExtFieldElem conjugate() const noexcept
        requires(DEGREE == 2)
    {
        return ExtFieldElem({coeffs[0], -coeffs[1]});
    }

    static constexpr ExtFieldElem one() noexcept
    {
        ExtFieldElem res;
        res.coeffs[0] = ValueT::one();
        return res;
    }

    constexpr ExtFieldElem inv() const noexcept { return inverse(*this); }

    friend constexpr ExtFieldElem operator+(const ExtFieldElem& e1, const ExtFieldElem& e2) noexcept
    {
        auto res = e1.coeffs;
        for (size_t i = 0; i < DEGREE; ++i)
            res[i] = res[i] + e2.coeffs[i];
        return ExtFieldElem(res);
    }

    friend constexpr ExtFieldElem operator-(const ExtFieldElem& e1, const ExtFieldElem& e2) noexcept
    {
        auto res = e1.coeffs;
        for (size_t i = 0; i < DEGREE; ++i)
            res[i] = res[i] - e2.coeffs[i];
        return ExtFieldElem(res);
    }

    friend constexpr ExtFieldElem operator-(const ExtFieldElem& e) noexcept
    {
        CoeffArrT ret;
        for (size_t i = 0; i < DEGREE; ++i)
            ret[i] = -e.coeffs[i];
        return ExtFieldElem(ret);
    }

    [[gnu::always_inline]] friend constexpr ExtFieldElem operator*(
        const ExtFieldElem& e1, const ExtFieldElem& e2) noexcept
    {
        if constexpr (requires { sqr(e1); })  // Use sqr() if available.
        {
            if (&e1 == &e2)
                return sqr(e1);
        }
        return multiply(e1, e2);
    }

    friend constexpr bool operator==(
        const ExtFieldElem& e1, const ExtFieldElem& e2) noexcept = default;

    friend constexpr ExtFieldElem operator*(const ExtFieldElem& e, const Base& s) noexcept
    {
        auto res = e;
        for (auto& c : res.coeffs)
            c = c * s;
        return res;
    }
};

}  // namespace evmone::crypto::ecc
