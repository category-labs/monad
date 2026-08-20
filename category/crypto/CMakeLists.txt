# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Hash and signature primitives, in C so that they carry no dependency on
# monad_core. monad_core links this library for keccak256(), which its
# category/core/keccak.hpp wraps to return a monad::hash256.

add_library(monad_crypto STATIC)

monad_compile_options(monad_crypto)

target_sources(monad_crypto PRIVATE
  "hash256.h"
  "keccak.c"
  "keccak.h")

target_include_directories(monad_crypto PUBLIC "${CATEGORY_MAIN_DIR}")

# keccak256() is a thin wrapper over OpenSSL's SHA3 core: hand-written AVX2 /
# AVX-512 assembly on x86-64, portable C everywhere else.
target_include_directories(monad_crypto PRIVATE "${THIRD_PARTY_DIR}/openssl")
if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86_64")
  target_sources(monad_crypto PRIVATE "keccak_impl.S")
else()
  target_sources(monad_crypto
                 PRIVATE "${THIRD_PARTY_DIR}/openssl/crypto/sha/keccak1600.c")
endif()

# Precompiles vendored from silkpre: SHA-256, RIPEMD-160, BLAKE2F, ECRECOVER.
# The sources stay under third_party/ with their LICENSE and NOTICE
set(SILKPRE_VENDOR_DIR "${THIRD_PARTY_DIR}/silkpre_vendor/src")

target_sources(monad_crypto PRIVATE
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/blake2b.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/blake2b.h"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/ecdsa.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/ecdsa.h"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/rmd160.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/rmd160.h"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/sha256.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/sha256.h")

target_include_directories(monad_crypto PUBLIC "${SILKPRE_VENDOR_DIR}")

# ecdsa needs libsecp256k1
target_link_libraries(monad_crypto PUBLIC PkgConfig::secp256k1)

# Silence the warnings the vendored sources legitimately trip on; the upstream
# silkpre build doesn't enforce them.
set_source_files_properties(
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/blake2b.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/ecdsa.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/rmd160.c"
  "${SILKPRE_VENDOR_DIR}/category/crypto/silkpre_vendor/sha256.c"
  TARGET_DIRECTORY monad_crypto
  PROPERTIES COMPILE_OPTIONS "-Wno-conversion;-Wno-sign-conversion")