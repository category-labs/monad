// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

// Modified 2026 by Category Labs:
//   - alt_bn128 (EIP-196 / EIP-197) precompiles from test/state/precompiles.cpp
//   - Rename to use monad prefixes
//   - Return success as bool and write the result to a caller-provided buffer
//   - ecAdd inverts the slope denominator with GMP

#include "bn254_precompiles.hpp"

#include "bn254.hpp"

#include <gmp.h>

#include <algorithm>
#include <cassert>
#include <cstring>
#include <span>
#include <utility>
#include <vector>

namespace bn = evmone::crypto::bn254;

namespace
{
// ecc::add_affine inverts with a binary extended Euclid, which costs several
// times more than the rest of ecAdd; GMP's gcdext is much faster.
bn::Fq inverse(const bn::Fq& a) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t));
    static constexpr auto MOD = bn::Curve::FIELD_PRIME;
    static constexpr mp_limb_t mod_limbs[4]{MOD[0], MOD[1], MOD[2], MOD[3]};

    const auto v = a.value();
    const mp_limb_t limbs[4]{v[0], v[1], v[2], v[3]};
    mpz_t x, m, r;
    mpz_roinit_n(x, limbs, 4);
    mpz_roinit_n(m, mod_limbs, 4);
    mpz_init2(r, 256);
    [[maybe_unused]] const auto ok = mpz_invert(r, x, m);
    assert(ok);
    intx::uint256 inv;
    for (size_t i = 0; i != 4; ++i)
        inv[i] = mpz_getlimbn(r, static_cast<mp_size_t>(i));
    mpz_clear(r);
    return bn::Fq{inv};
}

// ecc::add_affine with the inversion above.
bn::AffinePoint add_affine(const bn::AffinePoint& p, const bn::AffinePoint& q) noexcept
{
    if (p == 0)
        return q;
    if (q == 0)
        return p;

    const auto& [x1, y1] = p;
    const auto& [x2, y2] = q;

    auto dx = x2 - x1;
    auto dy = y2 - y1;
    if (dx == 0)
    {
        if (dy != 0)    // For opposite points
            return {};  // return the point at infinity.

        // For coincident points find the slope of the tangent line.
        const auto xx = x1 * x1;
        dy = xx + xx + xx;
        dx = y1 + y1;
    }
    const auto slope = dy * inverse(dx);

    const auto xr = slope * slope - x1 - x2;
    const auto yr = slope * (x1 - xr) - y1;
    return {xr, yr};
}
}  // namespace

bool monad_bn_add(uint8_t out[64], uint8_t const *input, size_t len) noexcept
{
    uint8_t input_buffer[128]{};
    if (len != 0)
        std::memcpy(input_buffer, input, std::min(len, std::size(input_buffer)));

    const auto input_span = std::span{input_buffer};

    const auto p = bn::AffinePoint::from_bytes(input_span.subspan<0, 64>());
    const auto q = bn::AffinePoint::from_bytes(input_span.subspan<64, 64>());
    if (!p.has_value() || !q.has_value()) [[unlikely]]
        return false;
    if (!bn::validate(*p) || !bn::validate(*q)) [[unlikely]]
        return false;

    const auto res = add_affine(*p, *q);
    res.to_bytes(std::span<uint8_t, 64>{out, 64});
    return true;
}

bool monad_bn_mul(uint8_t out[64], uint8_t const *input, size_t len) noexcept
{
    uint8_t input_buffer[96]{};
    if (len != 0)
        std::memcpy(input_buffer, input, std::min(len, std::size(input_buffer)));

    const auto input_span = std::span{input_buffer};

    const auto p = bn::AffinePoint::from_bytes(input_span.subspan<0, 64>());
    if (!p.has_value() || !bn::validate(*p)) [[unlikely]]
        return false;

    const auto c = intx::be::unsafe::load<intx::uint256>(input_buffer + 64);

    const auto res = bn::mul(*p, c);
    res.to_bytes(std::span<uint8_t, 64>{out, 64});
    return true;
}

bool monad_snarkv(uint8_t out[32], uint8_t const *input, size_t len) noexcept
{
    static constexpr size_t PAIR_SIZE = 192;

    if (len % PAIR_SIZE != 0)
        return false;

    std::vector<std::pair<bn::AffinePoint, bn::ExtPoint>> pairs;
    pairs.reserve(len / PAIR_SIZE);
    for (auto input_ptr = input; input_ptr != input + len; input_ptr += PAIR_SIZE)
    {
        const auto p = bn::AffinePoint::from_bytes(std::span<const uint8_t, 64>{input_ptr, 64});
        if (!p.has_value()) [[unlikely]]
            return false;

        // G2 EVM ABI feeds the imaginary coefficient before the real one for each Fq²,
        // so swap the offsets when reading into (real, imaginary) order.
        const auto qx_real = bn::Fq::from_bytes(std::span<const uint8_t, 32>{input_ptr + 96, 32});
        const auto qx_imag = bn::Fq::from_bytes(std::span<const uint8_t, 32>{input_ptr + 64, 32});
        const auto qy_real = bn::Fq::from_bytes(std::span<const uint8_t, 32>{input_ptr + 160, 32});
        const auto qy_imag = bn::Fq::from_bytes(std::span<const uint8_t, 32>{input_ptr + 128, 32});
        if (!qx_real || !qx_imag || !qy_real || !qy_imag) [[unlikely]]
            return false;
        const bn::ExtPoint q{bn::Fq2({*qx_real, *qx_imag}), bn::Fq2({*qy_real, *qy_imag})};
        pairs.emplace_back(*p, q);
    }

    const auto res = bn::pairing_check(pairs);
    if (!res.has_value())
        return false;

    std::fill_n(out, 32, 0);
    out[31] = *res ? 1 : 0;
    return true;
}
