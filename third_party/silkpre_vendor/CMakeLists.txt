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

# SHA-256 and RIPEMD-160 implementations vendored from silkpre.
# See NOTICE and LICENSE.

add_library(monad_crypto STATIC)

monad_compile_options(monad_crypto)

target_sources(monad_crypto PRIVATE
  "src/silkpre_vendor/rmd160.c"
  "src/silkpre_vendor/rmd160.h"
  "src/silkpre_vendor/sha256.c"
  "src/silkpre_vendor/sha256.h"
)

# Consumers include the headers via `<silkpre_vendor/sha256.h>` etc.
target_include_directories(monad_crypto PUBLIC src/)

# Silence the warnings these vendored sources legitimately trip on; the
# upstream silkpre build doesn't enforce them.
target_compile_options(monad_crypto PRIVATE
  -Wno-conversion -Wno-sign-conversion)
