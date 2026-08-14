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
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <cryptopp/eccrypto.h>
#include <cryptopp/ecp.h>
#include <cryptopp/integer.h>
#include <cryptopp/oids.h>

#include <c-kzg-4844/trusted_setup.hpp>

#include <eip4844/eip4844.h>

#include <common/bytes.h>
#include <common/ret.h>

#include <evmc/evmc.h>

#include <silkpre_vendor/blake2b.h>
#include <silkpre_vendor/ecdsa.h>
#include <silkpre_vendor/rmd160.h>
#include <silkpre_vendor/sha256.h>

#include <setup/settings.h>
#include <setup/setup.h>

#include <stdio.h>

#include <silkpre/precompile.h>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <memory>
#include <optional>
#include <string_view>

namespace
{
    // The KZG trusted setup costs ~2 s to load: decompressing and subgroup-checking 4096 G1 + 65 G2
    // points, which `perf record` on a `--nblocks 0` run shows as 55 % of monad's startup CPU sitting in
    // blst's __mulx_mont_384. It is independent of database size (1.93 s against a fresh 8 GB db, 2.02 s
    // against a 440 GB one), which is what identifies it as binary initialisation rather than file
    // opening, and `load_trusted_setup_file`'s `0` is already c-kzg's cheapest precompute, so the load
    // itself has nothing left to tune.
    //
    // Only the point_evaluation precompile (0x0a) needs it, and most blocks never touch it — so it is
    // loaded on FIRST USE. For a producer that starts one process per block (--min-follow-batch 1) that
    // 2 s was being paid per block, over half of the chain->witness latency.
    //
    // A function-local static, not a checked global: initialisation of one is thread-safe by
    // [stmt.dcl]/4, and this is now reached from parallel transaction execution rather than from a
    // single-threaded main(). The previous check-then-act on a global optional had no such guarantee.
    KZGSettings const &trusted_setup()
    {
        static std::optional<KZGSettings> const setup =
            []() -> std::optional<KZGSettings> {
            auto const data = c_kzg_4844::trusted_setup_data();
            std::optional<KZGSettings> loaded;
            KZGSettings settings;
            FILE *fp = fmemopen((void *)(data.data()), data.size(), "r");
            if (fp) {
                if (load_trusted_setup_file(&settings, fp, 0) == C_KZG_OK) {
                    loaded.emplace(settings);
                }
                fclose(fp);
            }
            return loaded;
        }();
        // The setup is embedded in the binary, so a failure to load is a broken build, not a runtime
        // condition. Aborting keeps the old MONAD_ASSERT semantics: what moves is WHEN it is paid, not
        // what happens on failure. Returning a failure from the precompile instead would turn a broken
        // build into a wrong block result.
        MONAD_ASSERT(setup.has_value());
        return *setup;
    }

    monad::bytes32_t kzg_to_version_hashed(KZGCommitment const &commitment)
    {
        constexpr uint8_t VERSION_HASH_VERSION_KZG = 1;
        monad::bytes32_t h;
        monad_sha256(
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
        constexpr auto r = monad::from_hex<bytes64_t>(v);
        static_assert(r.has_value());
        return r.value();
    }
}

MONAD_NAMESPACE_BEGIN

// Forces the load and reports success. Kept because the tests call it to fail early and loudly
// (precompiles_test.cpp, blockchain_test.cpp); nothing on the production path needs to, since
// point_evaluation_execute loads on demand. Calling it from main() is what cost 2 s per process.
bool init_trusted_setup()
{
    trusted_setup();
    return true;
}

// TODO: remove silkpre
template <SilkpreRunFunction Func>
static inline PrecompileResult silkpre_execute(byte_string_view const input)
{
    auto const [output, output_size] = Func(input.data(), input.size());
    if (output == nullptr) {
        MONAD_ASSERT(output_size == 0);
        return {EVMC_PRECOMPILE_FAILURE, nullptr, 0};
    }
    return {EVMC_SUCCESS, output, output_size};
}

PrecompileResult ecrecover_execute(byte_string_view const input)
{
    byte_string d(128, 0);
    if (!input.empty()) {
        std::memcpy(d.data(), input.data(), std::min(input.size(), 128uz));
    }

    auto const v{load_be_unsafe<uint256_t>(&d[32])};
    auto const r{load_be_unsafe<uint256_t>(&d[64])};
    auto const s{load_be_unsafe<uint256_t>(&d[96])};

    if (!Secp256k1Signature{r, s}.has_valid_range() || (v != 27 && v != 28)) {
        return {EVMC_SUCCESS, nullptr, 0};
    }

    auto *const output = static_cast<uint8_t *>(std::calloc(1, 32));
    MONAD_ASSERT(output != nullptr);

    thread_local std::
        unique_ptr<secp256k1_context, void (*)(secp256k1_context *)> const
            context(
                secp256k1_context_create(MONAD_SECP256K1_CONTEXT_FLAGS),
                &secp256k1_context_destroy);

    if (!monad_recover_address(
            output + 12, &d[0], &d[64], v != 27, context.get())) {
        std::free(output);
        return {EVMC_SUCCESS, nullptr, 0};
    }
    return {EVMC_SUCCESS, output, 32};
}

PrecompileResult sha256_execute(byte_string_view const input)
{
    auto *const output = static_cast<uint8_t *>(std::malloc(32));
    MONAD_ASSERT(output != nullptr);

    monad_sha256(
        output,
        input.data(),
        input.size(),
        /*use_cpu_extensions=*/true);

    return {EVMC_SUCCESS, output, 32};
}

PrecompileResult ripemd160_execute(byte_string_view const input)
{
    auto *const output = static_cast<uint8_t *>(std::malloc(32));
    MONAD_ASSERT(output != nullptr);

    // Ethereum's RIPEMD-160 precompile returns the 20-byte digest left-padded
    // with 12 zero bytes to a 32-byte ABI word.
    std::memset(output, 0, 12);
    monad_rmd160(output + 12, input.data(), input.size());

    return {EVMC_SUCCESS, output, 32};
}

PrecompileResult ecadd_execute(byte_string_view const input)
{
    auto const clamped_input = input.substr(0, 128);
    return silkpre_execute<silkpre_bn_add_run>(clamped_input);
}

PrecompileResult ecmul_execute(byte_string_view const input)
{
    auto const clamped_input = input.substr(0, 96);
    return silkpre_execute<silkpre_bn_mul_run>(clamped_input);
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
    if (input.size() != 213) {
        return {EVMC_PRECOMPILE_FAILURE, nullptr, 0};
    }

    uint8_t const f{input[212]};
    if (f != 0 && f != 1) {
        return {EVMC_PRECOMPILE_FAILURE, nullptr, 0};
    }

    MonadBlake2bState state{};
    if (f) {
        state.f[0] = std::numeric_limits<uint64_t>::max();
    }

    static_assert(std::endian::native == std::endian::little);
    static_assert(sizeof(state.h) == 8 * 8);
    std::memcpy(&state.h, input.data() + 4, 8 * 8);

    uint8_t block[MONAD_BLAKE2B_BLOCKBYTES];
    std::memcpy(block, input.data() + 68, MONAD_BLAKE2B_BLOCKBYTES);

    std::memcpy(&state.t, input.data() + 196, 8 * 2);

    uint32_t const r{load_be_unsafe<uint32_t>(input.data())};
    monad_blake2b_compress(&state, block, r);

    auto *const output = static_cast<uint8_t *>(std::malloc(64));
    MONAD_ASSERT(output != nullptr);

    std::memcpy(&output[0], &state.h[0], 8 * 8);
    return {EVMC_SUCCESS, output, 64};
}

PrecompileResult point_evaluation_execute(byte_string_view const input)
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
    verify_kzg_proof(&ok, &commitment, z, y, proof, std::addressof(trusted_setup()));
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
