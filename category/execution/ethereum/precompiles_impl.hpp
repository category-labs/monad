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

#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/crypto/silkpre_vendor/blake2b.h>
#include <category/crypto/silkpre_vendor/bn128.hpp>
#include <category/crypto/silkpre_vendor/rmd160.h>
#include <category/crypto/silkpre_vendor/sha256.h>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/ec_key.h>
#include <openssl/ecdsa.h>
#include <openssl/err.h>

#include <c-kzg-4844/trusted_setup.hpp>

#include <eip4844/eip4844.h>

#include <common/bytes.h>
#include <common/ret.h>

#include <evmc/evmc.h>

#include <setup/settings.h>
#include <setup/setup.h>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <gmp.h>
#include <limits>
#include <optional>
#include <string_view>

namespace
{
    std::optional<KZGSettings> g_trustedSetup;

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

[[gnu::always_inline]] inline PrecompileImplResult
sha256_impl(byte_string_view input, std::span<uint8_t, 32> const out)
{
    monad_sha256(
        out.data(),
        input.data(),
        input.size(),
        /*use_cpu_extensions=*/true);
    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileImplResult
ripemd160_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    // Ethereum's RIPEMD-160 precompile returns the 20-byte digest left-padded
    // with 12 zero bytes to a 32-byte ABI word.
    std::memset(out.data(), 0, 12);
    monad_rmd160(&out[12], input.data(), input.size());

    return {out.data(), 32};
}

[[gnu::always_inline]] inline PrecompileImplResult
ecadd_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    if (!monad_bn_add(out.data(), input.data(), input.size())) {
        return PrecompileImplResult::failure();
    }
    return {out.data(), out.size()};
}

[[gnu::always_inline]] inline PrecompileImplResult
ecmul_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    if (!monad_bn_mul(out.data(), input.data(), input.size())) {
        return PrecompileImplResult::failure();
    }
    return {out.data(), out.size()};
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
    mpz_t b;
    mpz_init(b);
    if (base.size()) {
        mpz_import(b, base.size(), 1, 1, 0, 0, base.data());
    }

    mpz_t e;
    mpz_init(e);
    if (exp.size()) {
        mpz_import(e, exp.size(), 1, 1, 0, 0, exp.data());
    }

    mpz_t m;
    mpz_init(m);
    mpz_import(m, modulus.size(), 1, 1, 0, 0, modulus.data());

    if (mpz_sgn(m) == 0) {
        mpz_clear(m);
        mpz_clear(e);
        mpz_clear(b);

        return {out.data(), static_cast<size_t>(modulus.size())};
    }

    mpz_t result;
    mpz_init(result);

    mpz_powm(result, b, e, m);

    // export as little-endian
    mpz_export(out.data(), nullptr, -1, 1, 0, 0, result);
    // and convert to big-endian
    std::reverse(out.begin(), out.end());

    mpz_clear(result);
    mpz_clear(m);
    mpz_clear(e);
    mpz_clear(b);

    return {out.data(), modulus.size()};
}

[[gnu::always_inline]] inline PrecompileImplResult
snarkv_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    if (!monad_snarkv(out.data(), input.data(), input.size())) {
        return PrecompileImplResult::failure();
    }
    return {out.data(), out.size()};
}

[[gnu::always_inline]] inline PrecompileImplResult
blake2bf_impl(byte_string_view const input, std::span<uint8_t, 64> const out)
{
    if (input.size() != 213) {
        return PrecompileImplResult::failure();
    }

    uint8_t const f{input[212]};
    if (f != 0 && f != 1) {
        return PrecompileImplResult::failure();
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

    std::memcpy(out.data(), &state.h[0], 8 * 8);
    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult point_evaluation_impl(
    byte_string_view const input, std::span<uint8_t, 64> const out)
{
    if (input.size() != 192) {
        return PrecompileImplResult::failure();
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
        return PrecompileImplResult::failure();
    }

    bool ok{false};
    verify_kzg_proof(&ok, &commitment, z, y, proof, &g_trustedSetup.value());
    if (!ok) {
        return PrecompileImplResult::failure();
    }

    std::memcpy(
        out.data(), blob_precompile_return_value().bytes, sizeof(bytes64_t));
    return {out.data(), 64};
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g1_add_impl(
    byte_string_view const input, std::span<uint8_t, 128> const out)
{
    return bls12::add<bls12::G1>(input, out);
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g1_msm_impl(
    byte_string_view const input, std::span<uint8_t, 128> const out)
{
    return bls12::msm<bls12::G1>(input, out);
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g2_add_impl(
    byte_string_view const input, std::span<uint8_t, 256> const out)
{
    return bls12::add<bls12::G2>(input, out);
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_g2_msm_impl(
    byte_string_view const input, std::span<uint8_t, 256> const out)
{
    return bls12::msm<bls12::G2>(input, out);
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_pairing_check_impl(
    byte_string_view const input, std::span<uint8_t, 32> const out)
{
    return bls12::pairing_check(input, out);
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_map_fp_to_g1_impl(
    byte_string_view const input, std::span<uint8_t, 128> const out)
{
    return bls12::map_fp_to_g<bls12::G1>(input, out);
}

[[gnu::always_inline]] inline PrecompileImplResult bls12_map_fp2_to_g2_impl(
    byte_string_view const input, std::span<uint8_t, 256> const out)
{
    return bls12::map_fp_to_g<bls12::G2>(input, out);
}

// Rollup precompiles

// EIP-7951
[[gnu::always_inline]] inline PrecompileImplResult
p256_verify_impl(byte_string_view const input, std::span<uint8_t, 32> const out)
{
    if (input.size() != 160) {
        return PrecompileImplResult::failure();
    }

    EC_GROUP const *const group = EC_group_p256();
    static BIGNUM const *const p = [group] {
        BIGNUM *const p = BN_new();
        MONAD_ASSERT(p != nullptr);
        bool const curve_ok =
            EC_GROUP_get_curve_GFp(group, p, nullptr, nullptr, nullptr) == 1;
        MONAD_ASSERT(curve_ok);
        return p;
    }();

    bssl::UniquePtr<BIGNUM> r{BN_bin2bn(input.data() + 32, 32, nullptr)};
    bssl::UniquePtr<BIGNUM> s{BN_bin2bn(input.data() + 64, 32, nullptr)};
    bssl::UniquePtr<BIGNUM> const qx{BN_bin2bn(input.data() + 96, 32, nullptr)};
    bssl::UniquePtr<BIGNUM> const qy{
        BN_bin2bn(input.data() + 128, 32, nullptr)};
    bssl::UniquePtr<EC_POINT> const q{EC_POINT_new(group)};
    bssl::UniquePtr<EC_KEY> const key{EC_KEY_new()};
    bssl::UniquePtr<ECDSA_SIG> const sig{ECDSA_SIG_new()};
    MONAD_ASSERT(r && s && qx && qy && q && key && sig);

    // if not (0 < r < n and 0 < s < n): return
    BIGNUM const *const n = EC_GROUP_get0_order(group);
    if (BN_is_zero(r.get()) || BN_cmp(r.get(), n) >= 0) {
        return PrecompileImplResult::failure();
    }
    if (BN_is_zero(s.get()) || BN_cmp(s.get(), n) >= 0) {
        return PrecompileImplResult::failure();
    }

    // if not (0 ≤ qx < p and 0 ≤ qy < p): return
    if (BN_cmp(qx.get(), p) >= 0 || BN_cmp(qy.get(), p) >= 0) {
        return PrecompileImplResult::failure();
    }

    // Fails for any point not on the curve, (0, 0) included
    if (EC_POINT_set_affine_coordinates_GFp(
            group, q.get(), qx.get(), qy.get(), nullptr) != 1) {
        ERR_clear_error();
        return PrecompileImplResult::failure();
    }

    bool const group_ok = EC_KEY_set_group(key.get(), group) == 1;
    MONAD_ASSERT(group_ok);
    bool const key_ok = EC_KEY_set_public_key(key.get(), q.get()) == 1;
    MONAD_ASSERT(key_ok);
    bool const sig_ok =
        ECDSA_SIG_set0(sig.get(), r.release(), s.release()) == 1;
    MONAD_ASSERT(sig_ok);

    // SEC 1 v2 4.1.4: R' is not at infinity and R'.x ≡ r (mod n)
    if (ECDSA_do_verify(input.data(), 32, sig.get(), key.get()) != 1) {
        ERR_clear_error();
        return PrecompileImplResult::failure();
    }

    // Return 0x000...1
    std::memset(out.data(), 0, 32);
    out.data()[31] = 1;
    return {out.data(), 32};
}

MONAD_NAMESPACE_END
