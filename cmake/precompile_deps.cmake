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

# Shared setup for third-party libraries needed by the precompile
# implementations.  Included by both the root CMakeLists.txt (full build)
# and category/zkvm/CMakeLists.txt (standalone zkvm build).
#
# Expects THIRD_PARTY_DIR to be set by the caller.

# blst (BLS12-381)
include("${CMAKE_CURRENT_LIST_DIR}/blst.cmake")

# silkpre (brings in secp256k1, libff, gmp)
set(OPTIONAL_BUILD_TESTS OFF)
set(OLD_CMAKE_POLICY_VERSION_MINIMUM "${CMAKE_POLICY_VERSION_MINIMUM}")
set(CMAKE_POLICY_VERSION_MINIMUM "3.5")
add_subdirectory("${THIRD_PARTY_DIR}/silkpre" "${CMAKE_CURRENT_BINARY_DIR}/_silkpre")
set(CMAKE_POLICY_VERSION_MINIMUM "${OLD_CMAKE_POLICY_VERSION_MINIMUM}")
# Undo the ccache injection that silkpre/libff does
set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE)
set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK)

# c-kzg-4844
add_subdirectory("${THIRD_PARTY_DIR}/c-kzg-4844-builder" "${CMAKE_CURRENT_BINARY_DIR}/_c-kzg-4844")

# cryptopp (system library)
find_package(PkgConfig REQUIRED)
pkg_check_modules(crypto++ REQUIRED IMPORTED_TARGET libcrypto++)

# immer
option(immer_BUILD_TESTS OFF)
option(immer_BUILD_EXAMPLES OFF)
option(immer_BUILD_EXTRAS OFF)
add_subdirectory("${THIRD_PARTY_DIR}/immer" "${CMAKE_CURRENT_BINARY_DIR}/_immer" SYSTEM)

# nlohmann_json
add_subdirectory("${THIRD_PARTY_DIR}/nlohmann_json" "${CMAKE_CURRENT_BINARY_DIR}/_nlohmann_json" SYSTEM)

# unordered_dense
add_subdirectory("${THIRD_PARTY_DIR}/unordered_dense" "${CMAKE_CURRENT_BINARY_DIR}/_unordered_dense")

# asmjit
set(ASMJIT_STATIC ON)
add_subdirectory("${THIRD_PARTY_DIR}/asmjit" "${CMAKE_CURRENT_BINARY_DIR}/_asmjit")
