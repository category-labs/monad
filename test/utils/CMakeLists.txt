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

add_library(monad-test-utils)

target_sources(
  monad-test-utils
  PRIVATE db_parity_harness.cpp
          db_parity_harness.hpp
          from_json.cpp
          from_json.hpp
          json_state.cpp
          json_state.hpp
          test_state.hpp)

target_include_directories(
    monad-test-utils PRIVATE ${PROJECT_SOURCE_DIR}/test/unit/common/include
                             "${TOP_CURRENT_BINARY_DIR}/test")

target_link_libraries(monad-test-utils PUBLIC nlohmann_json::nlohmann_json
                                              monad_execution)

monad_compile_options(monad-test-utils)

# Self-proof: drive two MonadDB instances through the harness and confirm they
# agree (and that the harness catches divergence). Becomes MonadDB-vs-RocksDB at
# F9. Links only monad-test-utils (which pulls in monad_execution).
add_unit_test(
  TARGET test_db_parity_harness
  SOURCES test_db_parity_harness.cpp
  LIBRARIES monad-test-utils)
