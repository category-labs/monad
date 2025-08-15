// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <cryptopp/eccrypto.h>
#include <cryptopp/ecp.h>
#include <cryptopp/integer.h>
#include <cryptopp/nbtheory.h>
#include <cryptopp/oids.h>

#include <blst.h>

#include <c-kzg-4844/trusted_setup.hpp>

#include <eip4844/eip4844.h>

#include <evmc/evmc.h>
#include <evmc/hex.hpp>

#include <intx/intx.hpp>

#include <setup/settings.h>
#include <setup/setup.h>

#include <silkpre/precompile.h>
#include <silkpre/sha256.h>

#include <cstring>

namespace
{
    std::optional<KZGSettings> g_trustedSetup;

    constexpr size_t num_words(size_t const length)
    {
        constexpr size_t WORD_SIZE = 32;
        return (length + WORD_SIZE - 1) / WORD_SIZE;
    }

    monad::bytes32_t kzg_to_version_hashed(KZGCommitment const &commitment)
    {
        constexpr uint8_t VERSION_HASH_VERSION_KZG = 1;
        monad::bytes32_t h;
        silkpre_sha256(
            h.bytes,
            commitment.bytes,
            sizeof(KZGCommitment),
            true /* use_cpu_extensions */);
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
}

MONAD_NAMESPACE_BEGIN

bool init_trusted_setup()
{
    if (!g_trustedSetup.has_value()) {
        auto const setup = c_kzg_4844::trusted_setup_data();
        KZGSettings settings;
        FILE *fp = fmemopen((void *)(setup.data()), setup.size(), "r");
        if (fp) {
            if (load_trusted_setup_file(&settings, fp, 0) == C_KZG_OK) {
                g_trustedSetup.emplace(settings);
            }
            fclose(fp);
        }
    }
    return g_trustedSetup.has_value();
}

template <SilkpreRunFunction Func>
static inline PrecompileResult silkpre_execute(byte_string_view const input)
{
    auto const [output, output_size] = Func(input.data(), input.size());
    if (output == nullptr) {
        MONAD_DEBUG_ASSERT(output_size == 0);
        return {EVMC_PRECOMPILE_FAILURE, nullptr, 0};
    }
    return {EVMC_SUCCESS, output, output_size};
}

uint64_t
ecrecover_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_ecrec_gas(input.data(), input.size(), static_cast<int>(rev));
}

uint64_t sha256_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_sha256_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t
ripemd160_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_rip160_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t identity_gas_cost(byte_string_view const input, evmc_revision)
{
    // YP eqn 232
    return 15 + 3 * num_words(input.size());
}

uint64_t ecadd_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_bn_add_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t ecmul_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_bn_mul_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t snarkv_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_snarkv_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t
blake2bf_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_blake2_f_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t expmod_gas_cost(byte_string_view const input, evmc_revision const rev)
{
    return silkpre_expmod_gas(
        input.data(), input.size(), static_cast<int>(rev));
}

uint64_t point_evaluation_gas_cost(byte_string_view, evmc_revision)
{
    return 50'000;
}

uint64_t bls12_g1_add_gas_cost(byte_string_view, evmc_revision)
{
    return 375;
}

uint64_t bls12_g1_msm_gas_cost(byte_string_view const input, evmc_revision)
{
    static constexpr auto pair_size = bls12::G1::encoded_size + 32;

    auto const k = input.size() / pair_size;

    if (k == 0) {
        return 0;
    }

    return (k * 12'000 * bls12::msm_discount<bls12::G1>(k)) / 1000;
}

uint64_t bls12_g2_add_gas_cost(byte_string_view, evmc_revision)
{
    return 600;
}

uint64_t bls12_g2_msm_gas_cost(byte_string_view const input, evmc_revision)
{
    static constexpr auto pair_size = bls12::G2::encoded_size + 32;

    auto const k = input.size() / pair_size;

    if (k == 0) {
        return 0;
    }

    return (k * 22'500 * bls12::msm_discount<bls12::G2>(k)) / 1000;
}

uint64_t
bls12_pairing_check_gas_cost(byte_string_view const input, evmc_revision)
{
    static constexpr auto pair_size =
        bls12::G1::encoded_size + bls12::G2::encoded_size;

    auto const k = input.size() / pair_size;
    return 32'600 * k + 37'700;
}

uint64_t bls12_map_fp_to_g1_gas_cost(byte_string_view, evmc_revision)
{
    return 5500;
}

uint64_t bls12_map_fp2_to_g2_gas_cost(byte_string_view, evmc_revision)
{
    return 23800;
}

// Rollup precompiles
uint64_t p256_verify_gas_cost(byte_string_view, evmc_revision)
{
    return 6900;
}

PrecompileResult ecrecover_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_ecrec_run>(input);
}

PrecompileResult sha256_execute(byte_string_view const input)
{
    if (MONAD_UNLIKELY(input.data() == nullptr)) {
        // Passing a null pointer to the Silkpre sha256 implementation invokes
        // undefined behaviour. We sidestep the UB here by passing a pointer to
        // the empty string instead.
        byte_string_view const nonnull{
            reinterpret_cast<unsigned char const *>(""), 0UL};
        return silkpre_execute<silkpre_sha256_run>(nonnull);
    }
    return silkpre_execute<silkpre_sha256_run>(input);
}

PrecompileResult ripemd160_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_rip160_run>(input);
}

PrecompileResult ecadd_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_bn_add_run>(input);
}

PrecompileResult ecmul_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_bn_mul_run>(input);
}

PrecompileResult identity_execute(byte_string_view const input)
{
    if (input.empty()) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto *const output = static_cast<uint8_t *>(malloc(input.size()));
    MONAD_ASSERT(output != nullptr);
    memcpy(output, input.data(), input.size());
    return {EVMC_SUCCESS, output, input.size()};
}

PrecompileResult expmod_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_expmod_run>(input);
}

PrecompileResult snarkv_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_snarkv_run>(input);
}

PrecompileResult blake2bf_execute(byte_string_view const input)
{
    return silkpre_execute<silkpre_blake2_f_run>(input);
}

PrecompileResult point_evaluation_execute(byte_string_view input)
{
    if (input.size() != 192) {
        return PrecompileResult::failure();
    }

    bytes32_t versioned_hash;
    std::memcpy(versioned_hash.bytes, input.data(), sizeof(bytes32_t));

    auto const *const z =
        reinterpret_cast<Bytes32 const *>(input.substr(32).data());
    auto const *const y =
        reinterpret_cast<Bytes32 const *>(input.substr(64).data());
    auto const *const commitment_data =
        reinterpret_cast<KZGCommitment const *>(input.substr(96).data());
    auto const *const proof =
        reinterpret_cast<KZGProof const *>(input.substr(144).data());

    KZGCommitment commitment{*commitment_data};
    if (versioned_hash != kzg_to_version_hashed(commitment)) {
        return PrecompileResult::failure();
    }

    bool ok{false};
    verify_kzg_proof(&ok, &commitment, z, y, proof, &g_trustedSetup.value());
    if (!ok) {
        return PrecompileResult::failure();
    }

    auto *const output = static_cast<uint8_t *>(std::malloc(sizeof(bytes64_t)));
    MONAD_ASSERT(output != nullptr);
    std::memcpy(
        output, blob_precompile_return_value().bytes, sizeof(bytes64_t));

    return {
        .status_code = EVMC_SUCCESS,
        .obuf = output,
        .output_size = sizeof(bytes64_t),
    };
}

PrecompileResult bls12_g1_add_execute(byte_string_view const input)
{
    return bls12::add<bls12::G1>(input);
}

PrecompileResult bls12_g1_msm_execute(byte_string_view const input)
{
    return bls12::msm<bls12::G1>(input);
}

PrecompileResult bls12_g2_add_execute(byte_string_view const input)
{
    return bls12::add<bls12::G2>(input);
}

PrecompileResult bls12_g2_msm_execute(byte_string_view const input)
{
    return bls12::msm<bls12::G2>(input);
}

PrecompileResult bls12_pairing_check_execute(byte_string_view const input)
{
    return bls12::pairing_check(input);
}

PrecompileResult bls12_map_fp_to_g1_execute(byte_string_view const input)
{
    return bls12::map_fp_to_g<bls12::G1>(input);
}

PrecompileResult bls12_map_fp2_to_g2_execute(byte_string_view const input)
{
    return bls12::map_fp_to_g<bls12::G2>(input);
}

// Rollup precompiles

// EIP-7951
PrecompileResult p256_verify_execute(byte_string_view const input)
{
    using namespace CryptoPP;

    auto const empty_result = PrecompileResult{
        .status_code = EVMC_SUCCESS,
        .obuf = nullptr,
        .output_size = 0,
    };

    if (input.size() != 160) {
        return empty_result;
    }

    Integer h(input.data(), 32);
    Integer r(input.data() + 32, 32);
    Integer s(input.data() + 64, 32);
    Integer qx(input.data() + 96, 32);
    Integer qy(input.data() + 128, 32);

    DL_GroupParameters_EC<ECP> params(ASN1::secp256r1());
    auto const &ec = params.GetCurve();
    auto const &n = params.GetSubgroupOrder();
    auto const p_mod = ec.FieldSize();
    auto const &G = params.GetSubgroupGenerator();

    // if not (0 < r < n and 0 < s < n): return
    if (!(r > Integer::Zero() && r < n)) {
        return empty_result;
    }

    if (!(s > Integer::Zero() && s < n)) {
        return empty_result;
    }

    // if not (0 ≤ qx < p and 0 ≤ qy < p): return
    if (!(qx >= Integer::Zero() && qx < p_mod)) {
        return empty_result;
    }

    if (!(qy >= Integer::Zero() && qy < p_mod)) {
        return empty_result;
    }

    // if qy^2 ≢ qx^3 + a*qx + b (mod p): return
    if (!ec.VerifyPoint({qx, qy})) {
        return empty_result;
    }

    // if (qx, qy) == (0, 0): return
    if (qx.IsZero() && qy.IsZero()) {
        return empty_result;
    }

    // s1 = s^(-1) (mod n)
    auto const s1 = s.InverseMod(n);

    // R' = (h * s1) * G + (r * s1) * (qx, qy)
    auto const u1 = a_times_b_mod_c(h, s1, n);
    auto const u2 = a_times_b_mod_c(r, s1, n);

    auto const p1 = ec.Multiply(u1, G);
    auto const p2 = ec.Multiply(u2, {qx, qy});
    auto const r_prime = ec.Add(p1, p2);

    // If R' is at infinity: return
    if (r_prime.identity) {
        return empty_result;
    }

    // if R'.x ≢ r (mod n): return
    if (r_prime.x % n != r) {
        return empty_result;
    }

    // Return 0x000...1
    auto *const output_buf = static_cast<uint8_t *>(std::malloc(32));
    MONAD_ASSERT(output_buf != nullptr);
    std::memset(output_buf, 0, 32);

    output_buf[31] = 1;

    return {
        .status_code = EVMC_SUCCESS,
        .obuf = output_buf,
        .output_size = 32,
    };
}

MONAD_NAMESPACE_END
