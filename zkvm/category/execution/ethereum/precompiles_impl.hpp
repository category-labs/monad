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
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/precompiles.hpp>

#include <core/zkvm_accelerators.h>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <algorithm>
#include <cstdlib>
#include <cstring>

namespace
{
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

    zkvm_bytes_32 kzg_to_version_hashed(uint8_t const *commitment)
    {
        constexpr uint8_t VERSION_HASH_VERSION_KZG = 1;
        zkvm_bytes_32 h;
        if (zkvm_sha256(commitment, sizeof(zkvm_kzg_commitment), &h) !=
            ZKVM_EOK) {
            return zkvm_bytes_32{{}};
        }
        h.data[0] = VERSION_HASH_VERSION_KZG;
        return h;
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

    bool evm_g1_to_zkvm(uint8_t const *evm128, uint8_t *zkvm96)
    {
        return evm_fp_to_raw(evm128, zkvm96) &&
               evm_fp_to_raw(evm128 + 64, zkvm96 + 48);
    }

    void zkvm_g1_to_evm(uint8_t const *zkvm96, uint8_t *evm128)
    {
        raw_fp_to_evm(zkvm96, evm128);
        raw_fp_to_evm(zkvm96 + 48, evm128 + 64);
    }

    bool evm_g2_to_zkvm(uint8_t const *evm256, uint8_t *zkvm192)
    {
        return evm_fp_to_raw(evm256, zkvm192) &&
               evm_fp_to_raw(evm256 + 64, zkvm192 + 48) &&
               evm_fp_to_raw(evm256 + 128, zkvm192 + 96) &&
               evm_fp_to_raw(evm256 + 192, zkvm192 + 144);
    }

    void zkvm_g2_to_evm(uint8_t const *zkvm192, uint8_t *evm256)
    {
        raw_fp_to_evm(zkvm192, evm256);
        raw_fp_to_evm(zkvm192 + 48, evm256 + 64);
        raw_fp_to_evm(zkvm192 + 96, evm256 + 128);
        raw_fp_to_evm(zkvm192 + 144, evm256 + 192);
    }
}

MONAD_NAMESPACE_BEGIN

PrecompileResult alloc_success(size_t buf_size)
{
    auto *obuf = static_cast<uint8_t *>(std::malloc(buf_size));
    return {
        .status_code = EVMC_SUCCESS,
        .obuf = obuf,
        .output_size = buf_size,
    };
}

bool init_trusted_setup()
{
    return true;
}

[[gnu::always_inline]] inline PrecompileImplResult ecrecover_impl(
    std::span<uint8_t const, 32> const msg,
    std::span<uint8_t const, 64> const sig, uint8_t recid,
    std::span<uint8_t, 32> const out)
{
    auto const *msg_hash = reinterpret_cast<zkvm_bytes_32 const *>(msg.data());
    // TODO(dhil): Check `sig` is well-formed; the patch
    // before had subscript 64 on a `uint8_t[64]`, which I think was copy-pasted
    // from the previous implementation, but it used an array of length 128.
    auto const *signature =
        reinterpret_cast<zkvm_secp256k1_signature const *>(sig.data());

    zkvm_secp256k1_pubkey pubkey;

    if (zkvm_secp256k1_ecrecover(msg_hash, signature, recid, &pubkey) !=
        ZKVM_EOK) {
        return {out.data(), 0};
    }

    zkvm_bytes_32 key_hash;
    if (zkvm_keccak256(pubkey.data, 64, &key_hash) != ZKVM_EOK) {
        return {out.data(), 0};
    }

    std::memset(out.data(), 0, out.size());
    std::memcpy(out.data() + 12, key_hash.data + 12, 20);
    return {out.data(), 32};
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
    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileResult
identity_execute(byte_string_view const input)
{
    if (input.empty()) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto *const output = static_cast<uint8_t *>(std::malloc(input.size()));
    MONAD_ASSERT(output != nullptr);
    std::memcpy(output, input.data(), input.size());
    return {EVMC_SUCCESS, output, input.size()};
}

[[gnu::always_inline]] inline PrecompileImplResult expmod_impl(
    std::span<uint8_t> const base, std::span<uint8_t> const exp,
    std::span<uint8_t> const modulus, std::span<uint8_t> out)
{
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
    auto const *p1 = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[0]);
    auto const *p2 = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[64]);

    if (zkvm_bn254_g1_add(
            p1, p2, reinterpret_cast<zkvm_bn254_g1_point *>(out.data())) !=
        ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult
ecmul_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    alignas(8) uint8_t d[96];
    safe_copy(d, 96, input.data(), input.size(), 0);

    auto const *point = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[0]);
    auto const *scalar = reinterpret_cast<zkvm_bn254_scalar const *>(&d[64]);

    if (zkvm_bn254_g1_mul(
            point,
            scalar,
            reinterpret_cast<zkvm_bn254_g1_point *>(out.data())) != ZKVM_EOK) {
        return PrecompileImplResult::failure();
    }
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

    auto const commitment_versioned_hash =
        kzg_to_version_hashed(commitment->data);
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

[[gnu::always_inline]] inline PrecompileResult
bls12_g2_msm_execute(byte_string_view const input)
{
    auto const k = input.size() / 288;
    if (k == 0 || input.size() % 288 != 0) {
        return PrecompileResult::failure();
    }

    auto *pairs = static_cast<zkvm_bls12_381_g2_msm_pair *>(
        std::malloc(k * sizeof(zkvm_bls12_381_g2_msm_pair)));
    MONAD_ASSERT(pairs != nullptr);

    for (size_t i = 0; i < k; ++i) {
        auto const *entry = input.data() + i * 288;
        if (!evm_g2_to_zkvm(entry, pairs[i].point.data)) {
            std::free(pairs);
            return PrecompileResult::failure();
        }
        std::memcpy(pairs[i].scalar.data, entry + 256, 32);
    }

    zkvm_bls12_381_g2_point result_point;
    auto const status = zkvm_bls12_g2_msm(pairs, k, &result_point);
    std::free(pairs);

    if (status != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(256);
    zkvm_g2_to_evm(result_point.data, result.obuf);
    return result;
}

[[gnu::always_inline]] inline PrecompileResult
bls12_pairing_check_execute(byte_string_view const input)
{
    auto const k = input.size() / 384;
    if (input.size() % 384 != 0) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(32);
    if (k == 0) {
        result.obuf[31] = 1;
        return result;
    }

    auto *pairs = static_cast<zkvm_bls12_381_pairing_pair *>(
        std::malloc(k * sizeof(zkvm_bls12_381_pairing_pair)));
    MONAD_ASSERT(pairs != nullptr);

    for (size_t i = 0; i < k; ++i) {
        auto const *entry = input.data() + i * 384;
        if (!evm_g1_to_zkvm(entry, pairs[i].g1.data) ||
            !evm_g2_to_zkvm(entry + 128, pairs[i].g2.data)) {
            std::free(pairs);
            return PrecompileResult::failure();
        }
    }

    bool verified = false;
    auto const status = zkvm_bls12_pairing(pairs, k, &verified);
    std::free(pairs);

    if (status != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    result.obuf[31] = verified ? 1 : 0;
    return result;
}

[[gnu::always_inline]] inline PrecompileResult
bls12_map_fp_to_g1_execute(byte_string_view const input)
{
    if (input.size() != 64) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_fp fp;
    if (!evm_fp_to_raw(input.data(), fp.data)) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_g1_point result_point;
    if (zkvm_bls12_map_fp_to_g1(&fp, &result_point) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(128);
    zkvm_g1_to_evm(result_point.data, result.obuf);
    return result;
}

[[gnu::always_inline]] inline PrecompileResult
bls12_map_fp2_to_g2_execute(byte_string_view const input)
{
    if (input.size() != 128) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_fp2 fp2;
    if (!evm_fp_to_raw(input.data(), fp2.data) ||
        !evm_fp_to_raw(input.data() + 64, fp2.data + 48)) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_g2_point result_point;
    if (zkvm_bls12_map_fp2_to_g2(&fp2, &result_point) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(256);
    zkvm_g2_to_evm(result_point.data, result.obuf);
    return result;
}

[[gnu::always_inline]] inline PrecompileResult
p256_verify_execute(byte_string_view const input)
{
    if (input.size() != 160) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto const *msg =
        reinterpret_cast<zkvm_secp256r1_hash const *>(input.data());
    auto const *sig =
        reinterpret_cast<zkvm_secp256r1_signature const *>(input.data() + 32);
    auto const *pubkey =
        reinterpret_cast<zkvm_secp256r1_pubkey const *>(input.data() + 96);

    bool verified = false;
    if (zkvm_secp256r1_verify(msg, sig, pubkey, &verified) != ZKVM_EOK) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    if (!verified) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto result = alloc_success(32);
    result.obuf[31] = 1;
    return result;
}

MONAD_NAMESPACE_END
