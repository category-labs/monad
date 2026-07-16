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

# Vendored precompiles from silkpre:
#   SHA-256, RIPEMD-160, BLAKE2F, ECRECOVER
# See NOTICE and LICENSE.

add_library(monad_crypto STATIC)

monad_compile_options(monad_crypto)

target_sources(monad_crypto PRIVATE
  "src/silkpre_vendor/rmd160.c"
  "src/silkpre_vendor/rmd160.h"
  "src/silkpre_vendor/sha256.c"
  "src/silkpre_vendor/sha256.h"
  "src/silkpre_vendor/blake2b.c"
  "src/silkpre_vendor/blake2b.h"
  "src/silkpre_vendor/ecdsa.c"
  "src/silkpre_vendor/ecdsa.h"
)

# ecdsa needs libsecp256k1 and ethash
target_link_libraries(monad_crypto PUBLIC PkgConfig::secp256k1 ethash::keccak)

# Consumers include the headers via `<silkpre_vendor/sha256.h>` etc.
target_include_directories(monad_crypto PUBLIC src/)

# Silence the warnings these vendored sources legitimately trip on; the
# upstream silkpre build doesn't enforce them.
target_compile_options(monad_crypto PRIVATE
  -Wno-conversion -Wno-sign-conversion)
