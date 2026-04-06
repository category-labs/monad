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

cmake_minimum_required(VERSION 3.20)

project(triedb-driver)

# triedb_driver

if (NOT DEFINED MONAD_EXECUTION_DIR)
  message(FATAL_ERROR "MONAD_EXECUTION_DIR must be passed in by build.rs")
endif()

# This is the library already built by monad-cxx, so that we don't built it
# again
add_library(monad_execution_local SHARED IMPORTED)
set_target_properties(monad_execution_local PROPERTIES
  INTERFACE_INCLUDE_DIRECTORIES "${PROJECT_SOURCE_DIR}/../../../../"
  IMPORTED_LOCATION "${MONAD_EXECUTION_DIR}/libmonad_execution.so"
)

add_subdirectory("../../../../" "monad-execution-build"
)# needed for monad-trie

add_library(triedb_driver SHARED "${PROJECT_SOURCE_DIR}/include/triedb.h"
                                 "${PROJECT_SOURCE_DIR}/src/triedb.cpp")

target_include_directories(triedb_driver PUBLIC ${PROJECT_SOURCE_DIR}/include)

# Interface link monad_execution so that we'll take any configuration we need,
# but we won't build it
target_link_libraries(triedb_driver INTERFACE monad_execution)
target_link_libraries(triedb_driver PUBLIC monad_execution_local)
target_link_libraries(triedb_driver PUBLIC asmjit::asmjit evmc intx ethash::keccak 
                      nlohmann_json::nlohmann_json quill unordered_dense ankerl_hash)

monad_compile_options(triedb_driver)
