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

#include <category/core/int.hpp>
#include <category/crypto/silkpre_vendor/sha256.h>
#include <category/execution/monad/staking/util/rfc9380_secp256k1.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <initializer_list>
#include <utility>

MONAD_STAKING_ANONYMOUS_NAMESPACE_BEGIN

// RFC 9380, Section 8.7: secp256k1_XMD:SHA-256_SSWU_RO_.
constexpr uint256_t P =
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f_u256;
constexpr uint256_t MAP_A =
    0x3f8731abdd661adca08a5558f0f5d272e953d363cb6f0e5d405447c01a444533_u256;
constexpr uint256_t MAP_B = 1771;
constexpr uint256_t Z = P - 11;
constexpr uint256_t INVERSE_EXP = P - 2;
constexpr uint256_t SQRT_RATIO_EXP = (P - 3) / 4;
// Appendix F.2.1.2: c2 = sqrt(-Z), with P = 3 mod 4.
constexpr uint256_t SQRT_MINUS_Z =
    0x31fdf302724013e57ad13fb38f842afeec184f00a74789dd286729c8303c4a59_u256;
static_assert(mulmod(SQRT_MINUS_Z, SQRT_MINUS_Z, P) == P - Z);

uint256_t add(uint256_t const &x, uint256_t const &y)
{
    return addmod(x, y, P);
}

uint256_t negate(uint256_t const &x)
{
    return x == 0 ? uint256_t{0} : P - x;
}

uint256_t multiply(uint256_t const &x, uint256_t const &y)
{
    return mulmod(x, y, P);
}

uint256_t power(uint256_t const &base, uint256_t const &exponent)
{
    // Four-bit windows reduce multiplications for the fixed public exponents.
    std::array<uint256_t, 16> powers;
    powers[0] = 1;
    powers[1] = base;
    for (size_t i = 2; i < powers.size(); ++i) {
        powers[i] = multiply(powers[i - 1], base);
    }
    uint256_t result = 1;
    for (int bit = 252; bit >= 0; bit -= 4) {
        for (int i = 0; i < 4; ++i) {
            result = multiply(result, result);
        }
        result =
            multiply(result, powers[(exponent[bit / 64] >> (bit % 64)) & 15]);
    }
    return result;
}

// Each hash_to_field element is exactly 48 bytes (RFC 9380 Section 8.7).
uint256_t reduce_48(uint8_t const *bytes, uint256_t const &modulus)
{
    words_t<6> value{};
    for (size_t word = 0; word < value.size(); ++word) {
        value[word] = load_be_unsafe<uint64_t>(bytes + (5 - word) * 8);
    }
    return uint256_t{udivrem(value, modulus.as_words()).rem};
}

std::array<uint8_t, 32> sha256(byte_string_view const data)
{
    std::array<uint8_t, 32> digest{};
    monad_sha256(digest.data(), data.data(), data.size(), true);
    return digest;
}

// RFC 9380, Section 5.3.1. All callers use a short DST and at most two
// 48-byte field elements, so the oversize-DST and ell > 255 cases cannot occur.
template <size_t Length>
std::array<uint8_t, Length>
expand_xmd(byte_string_view const message, byte_string_view const dst)
{
    static_assert(Length == 48 || Length == 96);
    byte_string input;
    input.reserve(68 + message.size() + dst.size());
    input.resize(64, 0);
    input.append(message);
    input.push_back(static_cast<uint8_t>(Length >> 8));
    input.push_back(static_cast<uint8_t>(Length));
    input.push_back(0);
    input.append(dst);
    input.push_back(static_cast<uint8_t>(dst.size()));
    auto const b0 = sha256(input);

    std::array<uint8_t, 32 + 1 + 255 + 1> block{};
    std::copy(dst.begin(), dst.end(), block.begin() + 33);
    size_t const block_size = 34 + dst.size();
    block[block_size - 1] = static_cast<uint8_t>(dst.size());
    std::array<uint8_t, 32> previous{};
    std::array<uint8_t, Length> expanded{};
    for (size_t offset = 0; offset < Length; offset += 32) {
        for (size_t j = 0; j < 32; ++j) {
            block[j] = offset == 0 ? b0[j] : b0[j] ^ previous[j];
        }
        block[32] = static_cast<uint8_t>(offset / 32 + 1);
        previous = sha256({block.data(), block_size});
        std::copy_n(
            previous.data(),
            std::min(size_t{32}, Length - offset),
            expanded.data() + offset);
    }
    return expanded;
}

uint256_t inverse(uint256_t const &value)
{
    return power(value, INVERSE_EXP);
}

// Evaluate denominator^degree * f(numerator / denominator), without inversion.
uint256_t polynomial(
    uint256_t const &numerator, uint256_t const &denominator,
    std::initializer_list<uint256_t> coefficients)
{
    uint256_t value = 0;
    uint256_t scale = 1;
    for (auto const &coefficient : coefficients) {
        value = add(multiply(value, numerator), multiply(coefficient, scale));
        scale = multiply(scale, denominator);
    }
    return value;
}

struct Point
{
    uint256_t x;
    uint256_t y;
};

struct SwuPoint
{
    uint256_t xn;
    uint256_t xd;
    uint256_t y;
};

struct RationalPoint
{
    uint256_t xn;
    uint256_t xd;
    uint256_t yn;
    uint256_t yd;
};

// RFC 9380 Appendix F.2.1.2. The denominator is nonzero.
std::pair<bool, uint256_t>
sqrt_ratio(uint256_t const &numerator, uint256_t const &denominator)
{
    uint256_t const uv = multiply(numerator, denominator);
    uint256_t const radicand = multiply(multiply(denominator, denominator), uv);
    uint256_t const root = multiply(power(radicand, SQRT_RATIO_EXP), uv);
    bool const square =
        multiply(multiply(root, root), denominator) == numerator;
    return {square, square ? root : multiply(root, SQRT_MINUS_Z)};
}

// Appendix F.2, retaining x as a ratio as described in Appendix G.1.
SwuPoint map_swu(uint256_t const &u)
{
    uint256_t const zu2 = multiply(Z, multiply(u, u));
    uint256_t const sum = add(multiply(zu2, zu2), zu2);
    uint256_t const xn = multiply(MAP_B, add(sum, 1));
    uint256_t const xd = multiply(MAP_A, sum == 0 ? Z : negate(sum));
    uint256_t const xd2 = multiply(xd, xd);
    uint256_t const xd3 = multiply(xd2, xd);
    uint256_t const curve_numerator =
        add(multiply(xn, add(multiply(xn, xn), multiply(MAP_A, xd2))),
            multiply(MAP_B, xd3));
    auto const [square, root] = sqrt_ratio(curve_numerator, xd3);
    uint256_t y = square ? root : multiply(multiply(zu2, u), root);
    if ((u[0] & 1) != (y[0] & 1)) {
        y = negate(y);
    }
    return {square ? xn : multiply(zu2, xn), xd, y};
}

// RFC 9380, Appendix E.1: the secp256k1 3-isogeny.
std::optional<RationalPoint> iso_map(SwuPoint const &point)
{
    uint256_t const &x = point.xn;
    uint256_t const &d = point.xd;
    uint256_t const x_num = polynomial(
        x,
        d,
        {0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa88c_u256,
         0x534c328d23f234e6e2a413deca25caece4506144037c40314ecbd0b53d9dd262_u256,
         0x7d3d4c80bc321d5b9f315cea7fd44c5d595d2fc0bf63b92dfff1044f17c6581_u256,
         0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa8c7_u256});
    uint256_t const x_den = polynomial(
        x,
        d,
        {1,
         0xedadc6f64383dc1df7c4b2d51b54225406d36b641f5e41bbc52a56612a8c6d14_u256,
         0xd35771193d94918a9ca34ccbb7b640dd86cd409542f8487d9fe6b745781eb49b_u256});
    uint256_t const y_num = polynomial(
        x,
        d,
        {0x2f684bda12f684bda12f684bda12f684bda12f684bda12f684bda12f38e38d84_u256,
         0x29a6194691f91a73715209ef6512e576722830a201be2018a765e85a9ecee931_u256,
         0xc75e0c32d5cb7c0fa9d0a54b12a0a6d5647ab046d686da6fdffc90fc201d71a3_u256,
         0x4bda12f684bda12f684bda12f684bda12f684bda12f684bda12f684b8e38e23c_u256});
    uint256_t const y_den = polynomial(
        x,
        d,
        {1,
         0x6484aa716545ca2cf3a70c3fa8fe337e0a3d21162f0d6299a7bf8192bfd2a76f_u256,
         0x7a06534bb8bdb49fd5e9e6632722c2989467c1bfc8e8d978dfb425d2685c2573_u256,
         0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffff93b_u256});
    if (x_den == 0 || y_den == 0) {
        return std::nullopt; // Isogeny kernel maps to the point at infinity.
    }
    return RationalPoint{
        x_num, multiply(d, x_den), multiply(point.y, y_num), y_den};
}

std::optional<secp256k1_pubkey> parse_point(Point const &point)
{
    auto const x = store_be_as<bytes32_t>(point.x);
    auto const y = store_be_as<bytes32_t>(point.y);
    // Both coordinates are already known; compressed parsing would recover y
    // with another square root. This encoding is only the internal library
    // bridge.
    std::array<uint8_t, 65> encoded;
    encoded[0] = 4;
    std::copy_n(x.bytes, 32, encoded.begin() + 1);
    std::copy_n(y.bytes, 32, encoded.begin() + 33);
    secp256k1_pubkey parsed;
    if (secp256k1_ec_pubkey_parse(
            get_secp_context(), &parsed, encoded.data(), encoded.size()) != 1) {
        return std::nullopt;
    }
    return parsed;
}

MONAD_STAKING_ANONYMOUS_NAMESPACE_END

MONAD_STAKING_NAMESPACE_BEGIN

std::optional<secp256k1_pubkey>
hash_to_secp256k1(byte_string_view const message, byte_string_view const dst)
{
    if (dst.empty() || dst.size() > 255) {
        return std::nullopt;
    }
    auto const uniform = expand_xmd<96>(message, dst);
    std::array<std::optional<RationalPoint>, 2> points;
    std::array<uint256_t, 2> denominators{1, 1};
    for (size_t i = 0; i < points.size(); ++i) {
        uint256_t const u = reduce_48(uniform.data() + 48 * i, P);
        points[i] = iso_map(map_swu(u));
        if (points[i]) {
            denominators[i] = multiply(points[i]->xd, points[i]->yd);
        }
    }
    if (!points[0] && !points[1]) {
        return std::nullopt;
    }
    // Normalize both mapped points with one shared inversion.
    uint256_t const reciprocal =
        inverse(multiply(denominators[0], denominators[1]));
    std::array<std::optional<secp256k1_pubkey>, 2> mapped;
    for (size_t i = 0; i < points.size(); ++i) {
        if (points[i]) {
            auto const &point = *points[i];
            uint256_t const inv = multiply(reciprocal, denominators[1 - i]);
            mapped[i] = parse_point(Point{
                multiply(multiply(point.xn, point.yd), inv),
                multiply(multiply(point.yn, point.xd), inv)});
            if (!mapped[i]) {
                return std::nullopt;
            }
        }
    }
    if (!mapped[0]) {
        return mapped[1];
    }
    if (!mapped[1]) {
        return mapped[0];
    }
    secp256k1_pubkey const *terms[] = {&*mapped[0], &*mapped[1]};
    secp256k1_pubkey sum;
    if (secp256k1_ec_pubkey_combine(get_secp_context(), &sum, terms, 2) != 1) {
        return std::nullopt;
    }
    return sum;
}

std::optional<bytes32_t> hash_to_secp256k1_scalar(
    byte_string_view const message, byte_string_view const dst)
{
    if (dst.empty() || dst.size() > 255) {
        return std::nullopt;
    }
    auto const uniform = expand_xmd<48>(message, dst);
    return store_be_as<bytes32_t>(
        reduce_48(uniform.data(), SECP256K1_SCALAR_ORDER));
}

MONAD_STAKING_NAMESPACE_END
