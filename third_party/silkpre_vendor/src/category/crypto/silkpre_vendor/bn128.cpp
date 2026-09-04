/*
   Copyright 2022 The Silkpre Authors

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

// Modified 2026 by Category Labs:
//   - alt_bn128 (EIP-196 / EIP-197) precompiles from silkpre/precompile.cpp
//   - Rename to use monad prefixes
//   - Return the result in a caller-provided buffer instead of SilkpreOutput

#include <category/crypto/silkpre_vendor/bn128.hpp>

#include <gmp.h>

#include <algorithm>
#include <cstring>
#include <optional>
#include <string>

#include <libff/algebra/curves/alt_bn128/alt_bn128_pairing.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp>
#include <libff/common/profiling.hpp>

// Utility functions for zkSNARK related precompiled contracts.
// See Yellow Paper, Appendix E "Precompiled Contracts", as well as
// https://eips.ethereum.org/EIPS/eip-196
// https://eips.ethereum.org/EIPS/eip-197
using Scalar = libff::bigint<libff::alt_bn128_q_limbs>;

// Must be called prior to invoking any other method.
// May be called many times from multiple threads.
static void init_libff() noexcept {
    // magic static
    [[maybe_unused]] static bool initialized = []() noexcept {
        libff::inhibit_profiling_info = true;
        libff::inhibit_profiling_counters = true;
        libff::alt_bn128_pp::init_public_params();
        return true;
    }();
}

static Scalar to_scalar(const uint8_t bytes_be[32]) noexcept {
    mpz_t m;
    mpz_init(m);
    mpz_import(m, 32, /*order=*/1, /*size=*/1, /*endian=*/0, /*nails=*/0,
               bytes_be);
    Scalar out{m};
    mpz_clear(m);
    return out;
}

// Notation warning: Yellow Paper's p is the same libff's q.
// Returns x < p (YP notation).
static bool valid_element_of_fp(const Scalar &x) noexcept {
    return mpn_cmp(x.data, libff::alt_bn128_modulus_q.data,
                   libff::alt_bn128_q_limbs) < 0;
}

static std::optional<libff::alt_bn128_G1>
decode_g1_element(const uint8_t bytes_be[64]) noexcept {
    Scalar x{to_scalar(bytes_be)};
    if (!valid_element_of_fp(x)) {
        return {};
    }

    Scalar y{to_scalar(bytes_be + 32)};
    if (!valid_element_of_fp(y)) {
        return {};
    }

    if (x.is_zero() && y.is_zero()) {
        return libff::alt_bn128_G1::zero();
    }

    libff::alt_bn128_G1 point{x, y, libff::alt_bn128_Fq::one()};
    if (!point.is_well_formed()) {
        return {};
    }
    return point;
}

static std::optional<libff::alt_bn128_Fq2>
decode_fp2_element(const uint8_t bytes_be[64]) noexcept {
    // big-endian encoding
    Scalar c0{to_scalar(bytes_be + 32)};
    Scalar c1{to_scalar(bytes_be)};

    if (!valid_element_of_fp(c0) || !valid_element_of_fp(c1)) {
        return {};
    }

    return libff::alt_bn128_Fq2{c0, c1};
}

static std::optional<libff::alt_bn128_G2>
decode_g2_element(const uint8_t bytes_be[128]) noexcept {
    std::optional<libff::alt_bn128_Fq2> x{decode_fp2_element(bytes_be)};
    if (!x) {
        return {};
    }

    std::optional<libff::alt_bn128_Fq2> y{decode_fp2_element(bytes_be + 64)};
    if (!y) {
        return {};
    }

    if (x->is_zero() && y->is_zero()) {
        return libff::alt_bn128_G2::zero();
    }

    libff::alt_bn128_G2 point{*x, *y, libff::alt_bn128_Fq2::one()};
    if (!point.is_well_formed()) {
        return {};
    }

    if (!(libff::alt_bn128_G2::order() * point).is_zero()) {
        // wrong order, doesn't belong to the subgroup G2
        return {};
    }

    return point;
}

static void encode_g1_element(libff::alt_bn128_G1 p,
                              uint8_t out[64]) noexcept {
    std::memset(out, 0, 64);
    if (p.is_zero()) {
        return;
    }

    p.to_affine_coordinates();

    auto x{p.X.as_bigint()};
    auto y{p.Y.as_bigint()};

    // Here we convert little-endian data to big-endian output
    static_assert(sizeof(x.data) == 32);

    std::memcpy(&out[0], y.data, 32);
    std::memcpy(&out[32], x.data, 32);

    std::reverse(out, out + 64);
}

bool monad_bn_add(uint8_t out[64], const uint8_t *ptr, size_t len) {
    std::basic_string<uint8_t> input(128, '\0');
    if (len != 0) {
        std::memcpy(input.data(), ptr, std::min(len, 128uz));
    }

    init_libff();

    std::optional<libff::alt_bn128_G1> x{decode_g1_element(input.data())};
    if (!x) {
        return false;
    }

    std::optional<libff::alt_bn128_G1> y{decode_g1_element(&input[64])};
    if (!y) {
        return false;
    }

    libff::alt_bn128_G1 sum{*x + *y};
    encode_g1_element(sum, out);
    return true;
}

bool monad_bn_mul(uint8_t out[64], const uint8_t *ptr, size_t len) {
    std::basic_string<uint8_t> input(96, '\0');
    if (len != 0) {
        std::memcpy(input.data(), ptr, std::min(len, 96uz));
    }

    init_libff();

    std::optional<libff::alt_bn128_G1> x{decode_g1_element(input.data())};
    if (!x) {
        return false;
    }

    Scalar n{to_scalar(&input[64])};

    libff::alt_bn128_G1 product{n * *x};
    encode_g1_element(product, out);
    return true;
}

static constexpr size_t kSnarkvStride{192};

bool monad_snarkv(uint8_t out[32], const uint8_t *input, size_t len) {
    if (len % kSnarkvStride != 0) {
        return false;
    }
    size_t k{len / kSnarkvStride};

    init_libff();
    using namespace libff;

    static const auto one{alt_bn128_Fq12::one()};
    auto accumulator{one};

    for (size_t i{0}; i < k; ++i) {
        std::optional<alt_bn128_G1> a{
            decode_g1_element(&input[i * kSnarkvStride])};
        if (!a) {
            return false;
        }
        std::optional<alt_bn128_G2> b{
            decode_g2_element(&input[i * kSnarkvStride + 64])};
        if (!b) {
            return false;
        }

        if (a->is_zero() || b->is_zero()) {
            continue;
        }

        accumulator = accumulator * alt_bn128_miller_loop(
                                        alt_bn128_precompute_G1(*a),
                                        alt_bn128_precompute_G2(*b));
    }

    std::memset(out, 0, 32);
    if (alt_bn128_final_exponentiation(accumulator) == one) {
        out[31] = 1;
    }
    return true;
}
