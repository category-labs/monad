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

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/zkvm/zkvm_accelerators.h>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>
#include <intx/intx.hpp>

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

    // Allocate a PrecompileResult with zeroed output buffer.
    monad::PrecompileResult alloc_success(size_t size)
    {
        if (size == 0) {
            return {EVMC_SUCCESS, nullptr, 0};
        }
        auto *buf = static_cast<uint8_t *>(std::malloc(size));
        std::memset(buf, 0, size);
        return {EVMC_SUCCESS, buf, size};
    }

    evmc::bytes32 kzg_to_version_hashed(uint8_t const *commitment)
    {
        constexpr uint8_t VERSION_HASH_VERSION_KZG = 1;
        evmc::bytes32 h;
        zkvm_sha256(
            commitment,
            sizeof(zkvm_kzg_commitment),
            reinterpret_cast<zkvm_sha256_hash *>(&h));
        h.bytes[0] = VERSION_HASH_VERSION_KZG;
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
        constexpr auto r = evmc::from_hex<bytes64_t>(v);
        static_assert(r.has_value());
        return r.value();
    }

    // Strip 16-byte zero padding from EVM BLS12 Fp (64B) to raw Fp (48B).
    bool evm_fp_to_raw(uint8_t const *evm64, uint8_t *raw48)
    {
        for (int i = 0; i < 16; ++i) {
            if (evm64[i] != 0) {
                return false;
            }
        }
        std::memcpy(raw48, evm64 + 16, 48);
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

bool init_trusted_setup()
{
    return true;
}

ImplOutput ecrecover_impl(const uint8_t msg[32],
                          const uint8_t sig[64],
                          uint8_t recid,
                          uint8_t out[20])
{
    auto const *msg_hash = reinterpret_cast<zkvm_bytes_32 const *>(&msg[0]);
    auto const *signature =
        reinterpret_cast<zkvm_secp256k1_signature const *>(&sig[64]);

    zkvm_secp256k1_pubkey pubkey;

    if (zkvm_secp256k1_ecrecover(msg_hash, signature, recid, &pubkey) !=
        ZKVM_EOK) {
        return {out, 0};
    }

    zkvm_bytes_32 key_hash;
    if (zkvm_keccak256(pubkey.data, 64, &key_hash) != ZKVM_EOK) {
        return {out, 0};
    }

    std::memcpy(out + 12, key_hash.data + 12, 20);
    return {out, 32};
}

PrecompileResult sha256_execute(byte_string_view const input)
{
    auto result = alloc_success(32);
    if (zkvm_sha256(
            input.data(),
            input.size(),
            reinterpret_cast<zkvm_bytes_32 *>(result.obuf)) != ZKVM_EOK) {
        return {EVMC_SUCCESS, nullptr, 0};
    }
    return result;
}

PrecompileResult ripemd160_execute(byte_string_view const input)
{
    auto result = alloc_success(32);
    zkvm_ripemd160(
        input.data(),
        input.size(),
        reinterpret_cast<zkvm_ripemd160_hash *>(result.obuf));
    return result;
}

PrecompileResult identity_execute(byte_string_view const input)
{
    if (input.empty()) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto *const output = static_cast<uint8_t *>(std::malloc(input.size()));
    MONAD_ASSERT(output != nullptr);
    std::memcpy(output, input.data(), input.size());
    return {EVMC_SUCCESS, output, input.size()};
}

PrecompileResult expmod_execute(byte_string_view const input)
{
    uint8_t lengths[96];
    safe_copy(lengths, 96, input.data(), input.size(), 0);

    uint64_t const base_len = u64_be::unsafe_from(&lengths[24]).native();
    uint64_t const exp_len = u64_be::unsafe_from(&lengths[56]).native();
    uint64_t const mod_len = u64_be::unsafe_from(&lengths[88]).native();

    if (mod_len == 0) {
        return {EVMC_SUCCESS, static_cast<uint8_t *>(std::malloc(1)), 0};
    }

    auto const data = input.data() + 96;
    auto result = alloc_success(mod_len);
    zkvm_modexp(
        data,
        base_len,
        data + base_len,
        exp_len,
        data + base_len + exp_len,
        mod_len,
        result.obuf);
    return result;
}

PrecompileResult ecadd_execute(byte_string_view const input)
{
    uint8_t d[128];
    safe_copy(d, 128, input.data(), input.size(), 0);

    auto const *p1 = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[0]);
    auto const *p2 = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[64]);

    auto result = alloc_success(64);
    if (zkvm_bn254_g1_add(
            p1, p2, reinterpret_cast<zkvm_bn254_g1_point *>(result.obuf)) !=
        ZKVM_EOK) {
        return PrecompileResult::failure();
    }
    return result;
}

PrecompileResult ecmul_execute(byte_string_view const input)
{
    uint8_t d[96];
    safe_copy(d, 96, input.data(), input.size(), 0);

    auto const *point = reinterpret_cast<zkvm_bn254_g1_point const *>(&d[0]);
    auto const *scalar = reinterpret_cast<zkvm_bn254_scalar const *>(&d[64]);

    auto result = alloc_success(64);
    if (zkvm_bn254_g1_mul(
            point,
            scalar,
            reinterpret_cast<zkvm_bn254_g1_point *>(result.obuf)) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }
    return result;
}

PrecompileResult snarkv_execute(byte_string_view const input)
{
    auto const k = input.size() / 192;

    auto result = alloc_success(32);
    if (k == 0) {
        result.obuf[31] = 1;
        return result;
    }

    auto const *pairs =
        reinterpret_cast<zkvm_bn254_pairing_pair const *>(input.data());
    bool verified = false;
    if (zkvm_bn254_pairing(pairs, k, &verified) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    result.obuf[31] = verified ? 1 : 0;
    return result;
}

PrecompileResult blake2bf_execute(byte_string_view const input)
{
    if (input.size() != 213) {
        return PrecompileResult::failure();
    }

    uint8_t const f = input[212];
    if (f != 0 && f != 1) {
        return PrecompileResult::failure();
    }

    uint32_t const rounds = u32_be::unsafe_from(input.data()).native();

    auto result = alloc_success(64);
    std::memcpy(result.obuf, input.data() + 4, 64);

    auto *h = reinterpret_cast<zkvm_blake2f_state *>(result.obuf);
    auto const *m =
        reinterpret_cast<zkvm_blake2f_message const *>(input.data() + 68);
    auto const *t =
        reinterpret_cast<zkvm_blake2f_offset const *>(input.data() + 196);

    if (zkvm_blake2f(rounds, h, m, t, f) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    return result;
}

PrecompileResult point_evaluation_execute(byte_string_view input)
{
    if (input.size() != 192) {
        return PrecompileResult::failure();
    }

    evmc::bytes32 versioned_hash;
    std::memcpy(versioned_hash.bytes, input.data(), sizeof(evmc::bytes32));

    auto const *const z = reinterpret_cast<zkvm_kzg_field_element const *>(
        input.substr(32).data());
    auto const *const y = reinterpret_cast<zkvm_kzg_field_element const *>(
        input.substr(64).data());
    auto const *const commitment_data = input.substr(96).data();
    auto const *const commitment =
        reinterpret_cast<zkvm_kzg_commitment const *>(commitment_data);
    auto const *const proof =
        reinterpret_cast<zkvm_kzg_proof const *>(input.substr(144).data());

    if (versioned_hash != kzg_to_version_hashed(commitment_data)) {
        return PrecompileResult::failure();
    }

    bool ok{false};
    zkvm_kzg_point_eval(commitment, z, y, proof, &ok);
    if (!ok) {
        return PrecompileResult::failure();
    }

    auto *const output =
        static_cast<uint8_t *>(std::malloc(sizeof(zkvm_bytes_64)));
    MONAD_ASSERT(output != nullptr);
    std::memcpy(
        output, blob_precompile_return_value().bytes, sizeof(zkvm_bytes_64));

    return {
        .status_code = EVMC_SUCCESS,
        .obuf = output,
        .output_size = sizeof(zkvm_bytes_64),
    };
}

PrecompileResult bls12_g1_add_execute(byte_string_view const input)
{
    if (input.size() != 256) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_g1_point p1, p2;
    if (!evm_g1_to_zkvm(input.data(), p1.data) ||
        !evm_g1_to_zkvm(input.data() + 128, p2.data)) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_g1_point result_point;
    if (zkvm_bls12_g1_add(&p1, &p2, &result_point) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(128);
    zkvm_g1_to_evm(result_point.data, result.obuf);
    return result;
}

PrecompileResult bls12_g1_msm_execute(byte_string_view const input)
{
    auto const k = input.size() / 160;
    if (k == 0 || input.size() % 160 != 0) {
        return PrecompileResult::failure();
    }

    auto *pairs = static_cast<zkvm_bls12_381_g1_msm_pair *>(
        std::malloc(k * sizeof(zkvm_bls12_381_g1_msm_pair)));
    MONAD_ASSERT(pairs != nullptr);
    for (size_t i = 0; i < k; ++i) {
        auto const *entry = input.data() + i * 160;
        if (!evm_g1_to_zkvm(entry, pairs[i].point.data)) {
            std::free(pairs);
            return PrecompileResult::failure();
        }
        std::memcpy(pairs[i].scalar.data, entry + 128, 32);
    }

    zkvm_bls12_381_g1_point result_point;
    auto const status = zkvm_bls12_g1_msm(pairs, k, &result_point);
    std::free(pairs);

    if (status != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(128);
    zkvm_g1_to_evm(result_point.data, result.obuf);
    return result;
}

PrecompileResult bls12_g2_add_execute(byte_string_view const input)
{
    if (input.size() != 512) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_g2_point p1, p2;
    if (!evm_g2_to_zkvm(input.data(), p1.data) ||
        !evm_g2_to_zkvm(input.data() + 256, p2.data)) {
        return PrecompileResult::failure();
    }

    zkvm_bls12_381_g2_point result_point;
    if (zkvm_bls12_g2_add(&p1, &p2, &result_point) != ZKVM_EOK) {
        return PrecompileResult::failure();
    }

    auto result = alloc_success(256);
    zkvm_g2_to_evm(result_point.data, result.obuf);
    return result;
}

PrecompileResult bls12_g2_msm_execute(byte_string_view const input)
{
    auto const k = input.size() / 288;
    if (k == 0 || input.size() % 288 != 0) {
        return PrecompileResult::failure();
    }

    auto *pairs = static_cast<zkvm_bls12_381_g2_msm_pair *>(
        std::malloc(k * sizeof(zkvm_bls12_381_g2_msm_pair)));

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

PrecompileResult bls12_pairing_check_execute(byte_string_view const input)
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

PrecompileResult bls12_map_fp_to_g1_execute(byte_string_view const input)
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

PrecompileResult bls12_map_fp2_to_g2_execute(byte_string_view const input)
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

PrecompileResult p256_verify_execute(byte_string_view const input)
{
    if (input.size() != 160) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto const *msg = reinterpret_cast<zkvm_secp256r1_hash const *>(input.data());
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
