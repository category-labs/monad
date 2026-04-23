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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/crypto/init.hpp>

#include <c-kzg-4844/trusted_setup.hpp>
#include <common/ret.h>
#include <setup/settings.h>
#include <setup/setup.h>

#include <openssl/evp.h>
#include <openssl/provider.h>

#include <quill/Quill.h>

#include <cstdio>
#include <memory>
#include <mutex>
#include <optional>
#include <stdio.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constinit std::optional<KZGSettings> g_trusted_setup;
constinit EVP_MD const *g_sha256_md = nullptr;
constinit EVP_MD const *g_ripemd160_md = nullptr;

bool load_trusted_setup()
{
    if (!g_trusted_setup.has_value()) {
        auto const setup = c_kzg_4844::trusted_setup_data();
        KZGSettings settings;
        std::unique_ptr<FILE, int (*)(FILE *)> const fp{
            fmemopen(
                const_cast<void *>(static_cast<void const *>(setup.data())),
                setup.size(),
                "r"),
            &std::fclose};
        if (fp) {
            if (load_trusted_setup_file(&settings, fp.get(), 0) == C_KZG_OK) {
                g_trusted_setup.emplace(settings);
            }
        }
    }
    if (!g_trusted_setup.has_value()) {
        LOG_ERROR("init_crypto: failed to load KZG trusted setup");
        return false;
    }
    return true;
}

bool load_providers()
{
    if (OSSL_PROVIDER_load(nullptr, "default") == nullptr) {
        LOG_ERROR("init_crypto: failed to load OpenSSL default provider");
        return false;
    }
    if (OSSL_PROVIDER_load(nullptr, "legacy") == nullptr) {
        LOG_ERROR("init_crypto: failed to load OpenSSL legacy provider");
        return false;
    }
    return true;
}

// Fetch every digest consumed by consensus-critical code, so the hot
// precompile path can read a pointer instead of walking providers on every
// call. We want to fail fast at startup if the local OpenSSL is
// misconfigured (e.g. FIPS mode disabling a chain-mandated algorithm)
// rather than discover it mid-block: a runtime digest failure leaves no
// consensus-safe option, since aborting loses liveness and returning a
// precompile failure silently forks state away from nodes whose OpenSSL is
// healthy.
bool fetch_digests()
{
    g_sha256_md = EVP_MD_fetch(nullptr, "SHA256", nullptr);
    if (g_sha256_md == nullptr) {
        LOG_ERROR("init_crypto: required digest SHA256 is not available");
        return false;
    }
    g_ripemd160_md = EVP_MD_fetch(nullptr, "RIPEMD160", nullptr);
    if (g_ripemd160_md == nullptr) {
        LOG_ERROR("init_crypto: required digest RIPEMD160 is not available");
        return false;
    }
    return true;
}

bool init_crypto_impl()
{
    return load_trusted_setup() && load_providers() && fetch_digests();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

// init_crypto runs its side effects exactly once per process. This both
// serializes the non-thread-safe mutation of g_trusted_setup against any
// concurrent FFI callers and makes repeat calls cheap idempotent queries of
// the cached outcome, so a misconfigured node stays failed rather than
// re-attempting provider loads and accumulating leaked handles. Quill log
// macros are delegated to helpers called by the lambda because LOG_ERROR
// expanded directly in a lambda body misbehaves with the root-logger-only
// configuration.
bool init_crypto()
{
    static std::once_flag flag;
    static bool success = false;

    std::call_once(flag, [] { success = init_crypto_impl(); });

    return success;
}

KZGSettings const &kzg_trusted_setup()
{
    MONAD_ASSERT(g_trusted_setup.has_value());
    return g_trusted_setup.value();
}

EVP_MD const *sha256_md()
{
    MONAD_ASSERT(g_sha256_md != nullptr);
    return g_sha256_md;
}

EVP_MD const *ripemd160_md()
{
    MONAD_ASSERT(g_ripemd160_md != nullptr);
    return g_ripemd160_md;
}

MONAD_NAMESPACE_END
