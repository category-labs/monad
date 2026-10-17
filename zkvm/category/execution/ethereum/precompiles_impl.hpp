// Copyright (C) 2025-26 Category Labs, Inc.
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

// zkVM precompiles shim: implements the EVM precompile execute functions
// by calling through the zkvm_accelerators.h C interface to Rust FFI.

#pragma once

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/precompiles.hpp>

#include <c-interface-accelerators/zkvm_accelerators.h>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <algorithm>
#include <cstdlib>
#include <cstring>

#if defined(MONAD_ZKVM_ZISK)
// zkvm/zisk/src/bn254.rs: zkvm_bn254_g1_add and zkvm_bn254_g1_mul on
// little-endian limbs, a point x || y; false where they fail.
extern "C" bool
monad_zkvm_bn254_g1_add(uint64_t const *p1, uint64_t const *p2, uint64_t *out);
extern "C" bool
monad_zkvm_bn254_g1_mul(uint64_t const *p, uint64_t const *k, uint64_t *out);
#endif

namespace
{
#if defined(MONAD_ZKVM_ZISK)
    // `n` big-endian words as little-endian limbs, and back: a load or a
    // store and a byte swap a word, where zisklib's conversions take a load,
    // a shift and an or a byte.
    template <size_t n>
    [[gnu::always_inline]] inline void
    be_words_to_limbs(uint8_t const *const src, uint64_t *const limbs)
    {
        for (size_t i = 0; i < n; ++i) {
            limbs[n - 1 - i] = monad::load_be_unsafe<uint64_t>(src + 8 * i);
        }
    }

    template <size_t n>
    [[gnu::always_inline]] inline void
    limbs_to_be_words(uint64_t const *const limbs, uint8_t *const dst)
    {
        for (size_t i = 0; i < n; ++i) {
            uint64_t const w = monad::bswap(limbs[n - 1 - i]);
            std::memcpy(dst + 8 * i, &w, sizeof(w));
        }
    }
#endif

    // Read from input with zero-padding for short inputs.
    void safe_copy(
        uint8_t *dst, size_t dst_size, uint8_t const *src, size_t src_size,
        size_t offset)
    {
        std::memset(dst, 0, dst_size);
        if (offset < src_size) {
            auto const avail = src_size - offset;
            auto const to_copy = std::min(avail, dst_size);
            std::memcpy(dst, src + offset, to_copy);
        }
    }

    struct bytes64_t
    {
        uint8_t bytes[64];
    };

    constexpr bytes64_t blob_precompile_return_value()
    {
        constexpr std::string_view v{
            "0x0000000000000000000000000000000000000000000000000000000000001000"
            "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"};
        constexpr auto r = monad::from_hex<bytes64_t>(v);
        static_assert(r.has_value());
        return r.value();
    }

    // 48-byte type for the BLS12-381 field prime, satisfies the FixedBytes
    // concept so it can be initialised with from_hex.
    struct fp_bytes_t
    {
        uint8_t bytes[48];
    };

    // BLS12-381 field prime p per EIP-2537:
    // p =
    // 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
    inline constexpr fp_bytes_t BASE_FIELD_MODULUS =
        monad::from_hex<fp_bytes_t>(
            "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624"
            "1eabfffeb153ffffb9feffffffffaaab")
            .value();

    // 64-byte comparison buffer: 16 zero-padding bytes followed by the
    // 48-byte big-endian prime. Used by read_fp for the memcmp range check.
    inline constexpr std::array<uint8_t, 64> BASE_FIELD_MODULUS_BYTES = [] {
        std::array<uint8_t, 64> buf{};
        for (std::size_t i = 0; i < sizeof(BASE_FIELD_MODULUS.bytes); ++i) {
            buf[16 + i] = BASE_FIELD_MODULUS.bytes[i];
        }
        return buf;
    }();
    static_assert(BASE_FIELD_MODULUS_BYTES.size() == 64);

    // Strip 16-byte zero padding from EVM BLS12 Fp (64B) to raw Fp (48B).
    bool evm_fp_to_raw(uint8_t const *const evm64, uint8_t *raw48)
    {
        static constexpr size_t fp_encoded_offset = 16;

        // The field prime p is 384 bits, encoded in a 64-byte buffer with 16
        // bytes of leading zero padding (fp_encoded_offset). memcmp over all
        // 64 bytes performs a big-endian >= comparison: the padding zeros in
        // both the input and BASE_FIELD_MODULUS_BYTES ensure the upper 16
        // bytes never cause a false positive, so this rejects any input >= p.
        if (MONAD_UNLIKELY(
                std::memcmp(evm64, BASE_FIELD_MODULUS_BYTES.data(), 64) >= 0)) {
            return false;
        }

        for (size_t i = 0; i < fp_encoded_offset; ++i) {
            if (evm64[i] != 0) {
                return false;
            }
        }
        std::memcpy(raw48, evm64 + fp_encoded_offset, 48);
        return true;
    }

    void raw_fp_to_evm(uint8_t const *raw48, uint8_t *evm64)
    {
        std::memset(evm64, 0, 16);
        std::memcpy(evm64 + 16, raw48, 48);
    }

#if defined(MONAD_ZKVM_SP1)
    // EIP-2537 encodes the point at infinity as all-zero bytes, but SP1's
    // zkcrypto bls12_381 codec signals infinity with the flag bit (byte 0,
    // bit 6) and rejects an all-zero (0,0) as off-curve. Translate the raw
    // G1/G2 point between the two forms: on input, flag an all-zero point; on
    // output, an SP1 flagged-infinity result maps back to EVM all-zero.
    void sp1_flag_infinity(uint8_t *raw, size_t n)
    {
        if (std::ranges::all_of(
                std::span{raw, n}, [](auto b) { return b == 0; })) {
            raw[0] = 0x40;
        }
    }

    bool sp1_is_flagged_infinity(uint8_t const *raw, size_t n)
    {
        return raw[0] == 0x40 &&
               std::ranges::all_of(
                   std::span{raw + 1, n - 1}, [](auto b) { return b == 0; });
    }
#endif

    bool evm_g1_to_zkvm(uint8_t const *evm128, uint8_t *zkvm96)
    {
        if (!evm_fp_to_raw(evm128, zkvm96) ||
            !evm_fp_to_raw(evm128 + 64, zkvm96 + 48)) {
            return false;
        }
#if defined(MONAD_ZKVM_SP1)
        sp1_flag_infinity(zkvm96, 96);
#endif
        return true;
    }

    void zkvm_g1_to_evm(uint8_t const *zkvm96, uint8_t *evm128)
    {
#if defined(MONAD_ZKVM_SP1)
        if (sp1_is_flagged_infinity(zkvm96, 96)) {
            std::memset(evm128, 0, 128);
            return;
        }
#endif
        raw_fp_to_evm(zkvm96, evm128);
        raw_fp_to_evm(zkvm96 + 48, evm128 + 64);
    }

    bool evm_g2_to_zkvm(uint8_t const *evm256, uint8_t *zkvm192)
    {
#if defined(MONAD_ZKVM_SP1)
        // SP1's zkcrypto bls12_381 decoder expects each Fp2 as c1 || c0, but
        // EIP-2537 (and blst/ZisK) encode Fp2 as c0 || c1. Swap the two
        // components of each of x and y when converting for SP1.
        if (!evm_fp_to_raw(evm256 + 64, zkvm192) || // x.c1
            !evm_fp_to_raw(evm256, zkvm192 + 48) || // x.c0
            !evm_fp_to_raw(evm256 + 192, zkvm192 + 96) || // y.c1
            !evm_fp_to_raw(evm256 + 128, zkvm192 + 144)) { // y.c0
            return false;
        }
        sp1_flag_infinity(zkvm192, 192);
        return true;
#else
        return evm_fp_to_raw(evm256, zkvm192) &&
               evm_fp_to_raw(evm256 + 64, zkvm192 + 48) &&
               evm_fp_to_raw(evm256 + 128, zkvm192 + 96) &&
               evm_fp_to_raw(evm256 + 192, zkvm192 + 144);
#endif
    }

    void zkvm_g2_to_evm(uint8_t const *zkvm192, uint8_t *evm256)
    {
#if defined(MONAD_ZKVM_SP1)
        if (sp1_is_flagged_infinity(zkvm192, 192)) {
            std::memset(evm256, 0, 256);
            return;
        }
        // SP1 emits each Fp2 as c1 || c0; swap back to EVM's c0 || c1 (mirror
        // of evm_g2_to_zkvm).
        raw_fp_to_evm(zkvm192 + 48, evm256); // x.c0
        raw_fp_to_evm(zkvm192, evm256 + 64); // x.c1
        raw_fp_to_evm(zkvm192 + 144, evm256 + 128); // y.c0
        raw_fp_to_evm(zkvm192 + 96, evm256 + 192); // y.c1
#else
        raw_fp_to_evm(zkvm192, evm256);
        raw_fp_to_evm(zkvm192 + 48, evm256 + 64);
        raw_fp_to_evm(zkvm192 + 96, evm256 + 128);
        raw_fp_to_evm(zkvm192 + 144, evm256 + 192);
#endif
    }
}

#if defined(MONAD_ZKVM_AIRBENDER)
namespace
{
    // n <= 32 big-endian bytes as a number
    inline monad::uint256_t
    airbender_be256(uint8_t const *const p, size_t const n)
    {
        alignas(8) uint8_t buf[32] = {};
        std::memcpy(buf + 32 - n, p, n);
        return monad::uint256_t{
            monad::load_be_unsafe<uint64_t>(buf + 24),
            monad::load_be_unsafe<uint64_t>(buf + 16),
            monad::load_be_unsafe<uint64_t>(buf + 8),
            monad::load_be_unsafe<uint64_t>(buf)};
    }

    // out = a·b·2^-256 mod m, for odd m, a, b < m and np = -m^-1 mod 2^256:
    // Montgomery's REDC on the bigint circuit, no host round trip. With
    // t = a·b and u = t mod 2^256 · np mod 2^256, t + u·m is a multiple of
    // 2^256 below 2m·2^256; its high half, less m once if it reaches m.
    inline void airbender_mont_mul(
        monad::uint256_t &out, monad::uint256_t const &a,
        monad::uint256_t const &b, monad::uint256_t const &m,
        monad::uint256_t const &np) noexcept
    {
        using namespace monad::airbender_bigint;
        slot tl;
        slot th;
        slot u;
        slot vh;
        op(tl.v, a, MEMCOPY);
        op(th.v, a, MEMCOPY);
        op(tl.v, b, MUL_LOW);
        op(th.v, b, MUL_HIGH);
        op(u.v, tl.v, MEMCOPY);
        op(u.v, np, MUL_LOW);
        op(vh.v, u.v, MEMCOPY);
        op(u.v, m, MUL_LOW); // u·m mod 2^256
        op(vh.v, m, MUL_HIGH);
        // the low halves sum to 0 mod 2^256: carry unless both are zero
        uint32_t const c = op(tl.v, u.v, ADD);
        uint32_t const hi = op(th.v, vh.v, ADD | (c ? CARRY : 0u));
        op(out, th.v, MEMCOPY);
        uint32_t const borrow = op(out, m, SUB);
        if (!hi && borrow) {
            op(out, m, ADD); // it was below m already
        }
    }

    // base^exp mod m when m < 2^256 -- ZKsync OS's single-digit case
    // (basic_system modexp/advice/single_digit.rs): square and multiply with
    // mulmod, each product on the bigint circuit and reduced by the host's
    // quotient. The accelerator's num-bigint Montgomery loop took ~700K
    // cycles a call. False for a wider modulus, which the accelerator keeps.
    inline bool airbender_modexp256(
        std::span<uint8_t> const base, std::span<uint8_t> const exp,
        std::span<uint8_t> const modulus, std::span<uint8_t> const out)
    {
        size_t lead = 0;
        while (lead < modulus.size() && modulus[lead] == 0) {
            ++lead;
        }
        size_t const mlen = modulus.size() - lead;
        if (mlen > 32) {
            return false;
        }
        std::memset(out.data(), 0, out.size());
        alignas(32) monad::uint256_t const m =
            airbender_be256(modulus.data() + lead, mlen);
        if (m == 0 || m == 1) {
            return true; // everything is 0 modulo 0 (EIP-198) or 1
        }
        // The base from its most significant end, 32 bytes at a time:
        // b = (b·2^256 + chunk) mod m.
        alignas(32) monad::uint256_t b{0};
        size_t pos = 0;
        size_t n = base.size() % 32;
        if (n == 0) {
            n = 32;
        }
        while (pos < base.size()) {
            alignas(32) monad::uint256_t lo =
                airbender_be256(base.data() + pos, n);
            monad::airbender_wide_rem(lo, b, m);
            b = lo;
            pos += n;
            n = 32;
        }
        if (m[0] & 1) {
            // An odd modulus (a field prime, nearly always): every square
            // and multiply in Montgomery form on the circuit alone.
            using namespace monad::airbender_bigint;
            // np = -m^-1 mod 2^256 by Newton: m·m = 1 mod 8, and each step
            // doubles the bits that are right (3, 6, ..., 384).
            slot x;
            slot t;
            slot two;
            two.v = monad::uint256_t{2};
            op(x.v, m, MEMCOPY);
            for (int i = 0; i < 7; ++i) {
                op(t.v, m, MEMCOPY);
                op(t.v, x.v, MUL_LOW);
                op(t.v, two.v, SUB_AND_NEGATE); // 2 - m·x
                op(x.v, t.v, MUL_LOW);
            }
            op(x.v, zero, SUB_AND_NEGATE); // -x
            op(t.v, m, MEMCOPY);
            op(t.v, x.v, MUL_LOW);
            op(t.v, two.v, ADD); // m·np + 2 = 1 mod 2^256
            slot one;
            one.v = monad::uint256_t{1};
            MONAD_ASSERT(op(t.v, one.v, EQ) == 1);
            // R = 2^256 mod m from the host's checked quotient, R^2 mod m by
            // mulmod; the base into Montgomery form, b·R mod m.
            slot rm;
            slot rhi;
            rm.v = monad::uint256_t{0};
            rhi.v = monad::uint256_t{1};
            monad::airbender_wide_rem(rm.v, rhi.v, m);
            slot r2;
            r2.v = monad::mulmod(rm.v, rm.v, m);
            slot bm;
            airbender_mont_mul(bm.v, b, r2.v, m, x.v);
            // 1 in Montgomery form is R mod m
            slot acc;
            slot sq;
            op(acc.v, rm.v, MEMCOPY);
            for (uint8_t const byte : exp) {
                for (int bit = 7; bit >= 0; --bit) {
                    airbender_mont_mul(sq.v, acc.v, acc.v, m, x.v);
                    if ((byte >> bit) & 1) {
                        airbender_mont_mul(acc.v, sq.v, bm.v, m, x.v);
                    }
                    else {
                        op(acc.v, sq.v, MEMCOPY);
                    }
                }
            }
            // out of Montgomery form: acc·1·R^-1
            airbender_mont_mul(sq.v, acc.v, one.v, m, x.v);
            alignas(8) uint8_t be[32];
            for (size_t i = 0; i < 4; ++i) {
                uint64_t const w = monad::bswap(sq.v[3 - i]);
                std::memcpy(be + 8 * i, &w, sizeof(w));
            }
            size_t const k = std::min(out.size(), size_t{32});
            std::memcpy(out.data() + out.size() - k, be + 32 - k, k);
            return true;
        }
        // The exponent's bits from the most significant: x^0 is 1, 0^0 too.
        alignas(32) monad::uint256_t r{1};
        bool started = false;
        for (uint8_t const byte : exp) {
            for (int bit = 7; bit >= 0; --bit) {
                if (started) {
                    r = monad::mulmod(r, r, m);
                }
                if ((byte >> bit) & 1) {
                    r = started ? monad::mulmod(r, b, m) : b;
                    started = true;
                }
            }
        }
        // r < m < 2^(8·mlen), and out has mod_len >= mlen bytes
        alignas(8) uint8_t be[32];
        for (size_t i = 0; i < 4; ++i) {
            uint64_t const w = monad::bswap(r[3 - i]);
            std::memcpy(be + 8 * i, &w, sizeof(w));
        }
        size_t const k = std::min(out.size(), size_t{32});
        std::memcpy(out.data() + out.size() - k, be + 32 - k, k);
        return true;
    }
}
#endif

MONAD_NAMESPACE_BEGIN

// Non-inline to match the host header: precompiles.cpp is the single TU
// including this, and it must emit the symbol for other TUs (e.g. the
// precompile test guest) that call the declaration in precompiles.hpp.
bool init_trusted_setup()
{
    return true;
}

// Substitute a pointer to the empty string when `input.data()` is null.
static inline uint8_t const *nonnull_input_data(byte_string_view const input)
{
    return input.data() != nullptr ? input.data()
                                   : reinterpret_cast<uint8_t const *>("");
}

[[gnu::always_inline]] inline PrecompileImplResult
sha256_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    std::memset(out.data(), 0, 32);
    if (zkvm_sha256(
            nonnull_input_data(input),
            input.size(),
            reinterpret_cast<zkvm_bytes_32 *>(out.data())) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileImplResult
ripemd160_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    std::memset(out.data(), 0, 32);
    if (zkvm_ripemd160(
            nonnull_input_data(input),
            input.size(),
            reinterpret_cast<zkvm_ripemd160_hash *>(out.data())) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
    // The RIPEMD-160 precompile (0x03) returns the 20-byte digest right-aligned
    // in a 32-byte word: 12 leading zero bytes then the digest. The two zkVM
    // backends write their accelerator's digest to opposite ends of the word,
    // so normalise to that layout per backend after writing straight into out:
    //   - SP1 writes the digest into the FIRST 20 bytes (0..20), so shift it
    //     right into out[12..32] in place and zero the leading 12 bytes.
    //   - ZisK writes the digest into the LAST 20 bytes (12..32), which already
    //     matches the EVM layout, so leave it as written.
#if defined(MONAD_ZKVM_SP1)
    std::memmove(out.data() + 12, out.data(), 20);
    std::memset(out.data(), 0, 12);
#endif
    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileImplResult
identity_impl(byte_string_view const input, std::span<uint8_t> const out)
{
    MONAD_ASSERT(!input.empty());

    std::memcpy(out.data(), input.data(), input.size());
    return {out.data(), input.size()};
}

[[gnu::always_inline]] inline PrecompileImplResult expmod_impl(
    std::span<uint8_t> const base, std::span<uint8_t> const exp,
    std::span<uint8_t> const modulus, std::span<uint8_t> out)
{
#if defined(MONAD_ZKVM_AIRBENDER)
    if (airbender_modexp256(base, exp, modulus, out)) {
        return {out.data(), out.size()};
    }
#endif
    if (zkvm_modexp(
            base.data(),
            base.size(),
            exp.data(),
            exp.size(),
            modulus.data(),
            modulus.size(),
            out.data()) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
    return {out.data(), out.size()};
}

[[gnu::always_inline]] inline PrecompileImplResult
ecadd_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    alignas(8) uint8_t d[128];
    safe_copy(d, 128, input.data(), input.size(), 0);
#if defined(MONAD_ZKVM_ZISK)
    uint64_t p1[8];
    uint64_t p2[8];
    uint64_t r[8];
    be_words_to_limbs<4>(&d[0], p1);
    be_words_to_limbs<4>(&d[32], p1 + 4);
    be_words_to_limbs<4>(&d[64], p2);
    be_words_to_limbs<4>(&d[96], p2 + 4);
    if (!monad_zkvm_bn254_g1_add(p1, p2, r)) {
        return PrecompileImplResult::failure();
    }
    limbs_to_be_words<4>(r, out.data());
    limbs_to_be_words<4>(r + 4, out.data() + 32);
#else
    auto const *p1 = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[0]);
    auto const *p2 = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[64]);

    if (zkvm_bn254_g1_add(
            p1, p2, reinterpret_cast<zkvm_bn254_g1_point *>(out.data())) !=
        ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
#endif
    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult
ecmul_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    alignas(8) uint8_t d[96];
    safe_copy(d, 96, input.data(), input.size(), 0);

#if defined(MONAD_ZKVM_ZISK)
    uint64_t point[8];
    uint64_t scalar[4];
    uint64_t r[8];
    be_words_to_limbs<4>(&d[0], point);
    be_words_to_limbs<4>(&d[32], point + 4);
    be_words_to_limbs<4>(&d[64], scalar);
    if (!monad_zkvm_bn254_g1_mul(point, scalar, r)) {
        return PrecompileImplResult::failure();
    }
    limbs_to_be_words<4>(r, out.data());
    limbs_to_be_words<4>(r + 4, out.data() + 32);
#else
    auto const *point = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[0]);
    auto const *scalar = reinterpret_cast<zkvm_bn254_scalar const *>(&d[64]);

    if (zkvm_bn254_g1_mul(
            point,
            scalar,
            reinterpret_cast<zkvm_bn254_g1_point *>(out.data())) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
#endif
    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult
snarkv_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    auto const k = input.size() / 192;

    std::memset(out.data(), 0, 32);
    if (k == 0) {
        out.data()[31] = 1;
        return {out.data(), 32};
    }

    auto *pairs = static_cast<zkvm_bn254_pairing_pair *>(
        std::aligned_alloc(8, input.size()));
    MONAD_ASSERT(pairs != nullptr);
    std::memcpy(pairs, input.data(), input.size());
    bool verified = false;
    if (zkvm_bn254_pairing(pairs, k, &verified) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    out.data()[31] = verified ? 1 : 0;
    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileImplResult
blake2bf_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    if (input.size() != 213) {
        return PrecompileImplResult::failure();
    }

    uint8_t const f = input[212];
    if (f != 0 && f != 1) {
        return PrecompileImplResult::failure();
    }

    uint32_t const rounds = u32_be::unsafe_from(input.data()).native();

    std::memcpy(out.data(), input.data() + 4, 64);

    auto *h = reinterpret_cast<zkvm_blake2f_state *>(out.data());
    auto *m = static_cast<zkvm_blake2f_message *>(
        std::aligned_alloc(8, sizeof(zkvm_blake2f_message)));
    MONAD_ASSERT(m != nullptr);
    std::memcpy(m, input.data() + 68, sizeof(zkvm_blake2f_message));
    auto *t = static_cast<zkvm_blake2f_offset *>(
        std::aligned_alloc(8, sizeof(zkvm_blake2f_offset)));
    MONAD_ASSERT(t != nullptr);
    std::memcpy(t, input.data() + 196, sizeof(zkvm_blake2f_offset));

    if (zkvm_blake2f(rounds, h, m, t, f) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult
point_evaluation_impl(byte_string_view input, std::span<uint8_t, 64> const out)
{
    if (input.size() != 192) {
        return PrecompileImplResult::failure();
    }

    auto *aligned_input =
        static_cast<uint8_t *>(std::aligned_alloc(8, input.size()));
    MONAD_ASSERT(aligned_input != nullptr);
    std::memcpy(aligned_input, input.data(), input.size());

    auto const *const versioned_hash =
        reinterpret_cast<zkvm_bytes_32 const *>(aligned_input);
    auto const *const z =
        reinterpret_cast<zkvm_kzg_field_element const *>(aligned_input + 32);
    auto const *const y =
        reinterpret_cast<zkvm_kzg_field_element const *>(aligned_input + 64);
    auto const *const commitment =
        reinterpret_cast<zkvm_kzg_commitment const *>(aligned_input + 96);
    auto const *const proof =
        reinterpret_cast<zkvm_kzg_proof const *>(aligned_input + 144);

    zkvm_bytes_32 commitment_versioned_hash{};
    constexpr uint8_t VERSION_HASH_VERSION_KZG = 1;
    if (zkvm_sha256(
            commitment->data,
            sizeof(zkvm_kzg_commitment),
            &commitment_versioned_hash) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
    commitment_versioned_hash.data[0] = VERSION_HASH_VERSION_KZG;

    if (!std::equal(
            std::begin(versioned_hash->data),
            std::end(versioned_hash->data),
            std::begin(commitment_versioned_hash.data))) {
        return PrecompileImplResult::failure();
    }

    bool ok{false};
    if (zkvm_kzg_point_eval(commitment, z, y, proof, &ok) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
    if (!ok) {
        return PrecompileImplResult::failure();
    }

    std::memcpy(
        out.data(),
        blob_precompile_return_value().bytes,
        sizeof(zkvm_bytes_64));
    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g1_add_impl(
    byte_string_view const input, std::span<uint8_t, 128> const out)
{
    if (input.size() != 256) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_g1_point p1, p2;
    if (!evm_g1_to_zkvm(input.data(), p1.data) ||
        !evm_g1_to_zkvm(input.data() + 128, p2.data)) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_g1_point result_point;
    if (zkvm_bls12_g1_add(&p1, &p2, &result_point) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    zkvm_g1_to_evm(result_point.data, out.data());
    return {out.data(), 128};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g1_msm_impl(
    byte_string_view const input, std::span<uint8_t, 128> const out)
{
    auto const k = input.size() / 160;
    if (k == 0 || input.size() % 160 != 0) {
        return PrecompileImplResult::failure();
    }

    auto *pairs = static_cast<zkvm_bls12_381_g1_msm_pair *>(
        std::aligned_alloc(8, k * sizeof(zkvm_bls12_381_g1_msm_pair)));
    MONAD_ASSERT(pairs != nullptr);

    for (size_t i = 0; i < k; ++i) {
        auto const *entry = input.data() + i * 160;
        if (!evm_g1_to_zkvm(entry, pairs[i].point.data)) {
            std::free(pairs);
            return PrecompileImplResult::failure();
        }
        std::memcpy(pairs[i].scalar.data, entry + 128, 32);
    }

    zkvm_bls12_381_g1_point result_point;
    auto const status = zkvm_bls12_g1_msm(pairs, k, &result_point);
    std::free(pairs);

    if (status != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    zkvm_g1_to_evm(result_point.data, out.data());
    return {out.data(), 128};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g2_add_impl(
    byte_string_view const input, std::span<uint8_t, 256> const out)
{
    if (input.size() != 512) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_g2_point p1, p2;
    if (!evm_g2_to_zkvm(input.data(), p1.data) ||
        !evm_g2_to_zkvm(input.data() + 256, p2.data)) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_g2_point result_point;
    if (zkvm_bls12_g2_add(&p1, &p2, &result_point) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    zkvm_g2_to_evm(result_point.data, out.data());
    return {out.data(), 256};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g2_msm_impl(
    byte_string_view const input, std::span<uint8_t, 256> const out)
{
    auto const k = input.size() / 288;
    if (k == 0 || input.size() % 288 != 0) {
        return PrecompileImplResult::failure();
    }

    auto *pairs = static_cast<zkvm_bls12_381_g2_msm_pair *>(
        std::aligned_alloc(8, k * sizeof(zkvm_bls12_381_g2_msm_pair)));
    MONAD_ASSERT(pairs != nullptr);

    for (size_t i = 0; i < k; ++i) {
        auto const *entry = input.data() + i * 288;
        if (!evm_g2_to_zkvm(entry, pairs[i].point.data)) {
            std::free(pairs);
            return PrecompileImplResult::failure();
        }
        std::memcpy(pairs[i].scalar.data, entry + 256, 32);
    }

    zkvm_bls12_381_g2_point result_point;
    auto const status = zkvm_bls12_g2_msm(pairs, k, &result_point);
    std::free(pairs);

    if (status != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    zkvm_g2_to_evm(result_point.data, out.data());
    return {out.data(), 256};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_pairing_check_impl(
    byte_string_view const input, std::span<uint8_t, 32> const out)
{
    auto const k = input.size() / 384;
    if (input.size() % 384 != 0) {
        return PrecompileImplResult::failure();
    }

    if (k == 0) {
        return PrecompileImplResult::failure();
    }

    auto *pairs = static_cast<zkvm_bls12_381_pairing_pair *>(
        std::aligned_alloc(8, k * sizeof(zkvm_bls12_381_pairing_pair)));
    MONAD_ASSERT(pairs != nullptr);

    for (size_t i = 0; i < k; ++i) {
        auto const *entry = input.data() + i * 384;
        if (!evm_g1_to_zkvm(entry, pairs[i].g1.data) ||
            !evm_g2_to_zkvm(entry + 128, pairs[i].g2.data)) {
            std::free(pairs);
            return PrecompileImplResult::failure();
        }
    }

    bool verified = false;
    auto const status = zkvm_bls12_pairing(pairs, k, &verified);
    std::free(pairs);

    if (status != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    std::memset(out.data(), 0, 32);
    out.data()[31] = verified ? 1 : 0;
    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_map_fp_to_g1_impl(
    byte_string_view const input, std::span<uint8_t, 128> const out)
{
    if (input.size() != 64) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_fp fp;
    if (!evm_fp_to_raw(input.data(), fp.data)) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_g1_point result_point;
    if (zkvm_bls12_map_fp_to_g1(&fp, &result_point) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    zkvm_g1_to_evm(result_point.data, out.data());
    return {out.data(), 128};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_map_fp2_to_g2_impl(
    byte_string_view const input, std::span<uint8_t, 256> const out)
{
    if (input.size() != 128) {
        return PrecompileImplResult::failure();
    }

    zkvm_bls12_381_fp2 fp2;
#if defined(MONAD_ZKVM_SP1)
    // SP1's map_fp2_to_g2 expects Fp2 = c1 || c0 (see evm_g2_to_zkvm).
    if (!evm_fp_to_raw(input.data() + 64, fp2.data) ||
        !evm_fp_to_raw(input.data(), fp2.data + 48)) {
        return {nullptr, 0};
    }
#else
    if (!evm_fp_to_raw(input.data(), fp2.data) ||
        !evm_fp_to_raw(input.data() + 64, fp2.data + 48)) {
        return PrecompileImplResult::failure();
    }
#endif

    zkvm_bls12_381_g2_point result_point;
    if (zkvm_bls12_map_fp2_to_g2(&fp2, &result_point) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    zkvm_g2_to_evm(result_point.data, out.data());
    return {out.data(), 256};
}

[[gnu::always_inline]] inline PrecompileImplResult
p256_verify_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    if (input.size() != 160) {
        return PrecompileImplResult::failure();
    }

    auto *aligned_input =
        static_cast<uint8_t *>(std::aligned_alloc(8, input.size()));
    MONAD_ASSERT(aligned_input != nullptr);
    std::memcpy(aligned_input, input.data(), input.size());

    auto const *msg =
        reinterpret_cast<zkvm_secp256r1_hash const *>(aligned_input);
    auto const *sig =
        reinterpret_cast<zkvm_secp256r1_signature const *>(aligned_input + 32);
    auto const *pubkey =
        reinterpret_cast<zkvm_secp256r1_pubkey const *>(aligned_input + 96);

    bool verified = false;
    if (zkvm_secp256r1_verify(msg, sig, pubkey, &verified) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }

    if (!verified) {
        return PrecompileImplResult::failure();
    }

    std::memset(out.data(), 0, 32);
    out.data()[31] = 1;
    return {out.data(), 32};
}

MONAD_NAMESPACE_END
