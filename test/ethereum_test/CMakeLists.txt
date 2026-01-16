# Copyright (C) 2025 Category Labs, Inc.
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

include(ExternalProject)

ExternalProject_Add(
  ExecutionSpecTestFixtures
  URL "https://github.com/ethereum/execution-spec-tests/releases/download/v5.4.0/fixtures_develop.tar.gz"
  URL_HASH "SHA256=3e2b02d49fe903eda4fd8caca5cbf0d139c470e97e1de9a85299b1b034f97099"
  PREFIX ${CMAKE_BINARY_DIR}
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ""
  INSTALL_COMMAND ""
  LOG_DOWNLOAD ON)

add_executable(monad-ethereum-test)
target_link_libraries(monad-ethereum-test PRIVATE nlohmann_json::nlohmann_json
                                                  monad_execution GTest::gtest)
target_sources(
  monad-ethereum-test
  PRIVATE include/blockchain_test.hpp
          include/event.hpp
          include/from_json.hpp
          include/revision_map.hpp
          include/transaction_test.hpp
          src/blockchain_test.cpp
          src/event.cpp
          src/from_json.cpp
          src/main.cpp
          src/transaction_test.cpp)

target_include_directories(
  monad-ethereum-test PUBLIC ${PROJECT_SOURCE_DIR}/test/ethereum_test/include)
target_include_directories(
  monad-ethereum-test PUBLIC ${PROJECT_SOURCE_DIR}/test/unit/common/include)
target_include_directories(monad-ethereum-test
                           PRIVATE "${TOP_CURRENT_BINARY_DIR}/test")
monad_compile_options(monad-ethereum-test)

target_link_libraries(monad-ethereum-test PRIVATE monad_unit_test_common)

function(add_ethereum_test)
  set(ONE_VALUE_ARGS FORK)
  cmake_parse_arguments(ADD_ETHEREUM_TEST "" "${ONE_VALUE_ARGS}" "" ${ARGN})

  set(EXCLUSION_FILE
      "${CMAKE_CURRENT_SOURCE_DIR}/exclude/${ADD_ETHEREUM_TEST_FORK}.cmake")
  include(${EXCLUSION_FILE})
  set(TESTS_EXCLUDED "${ADD_ETHEREUM_TEST_FORK}_excluded_tests")

  list(JOIN ${TESTS_EXCLUDED} ":" TESTS_EXCLUDED)
  set(FILTER "-:${TESTS_EXCLUDED}")

  add_test(NAME ${ADD_ETHEREUM_TEST_FORK}_monad_ethereum_test
           COMMAND monad-ethereum-test --fork ${ADD_ETHEREUM_TEST_FORK}
                   --record-exec-events --gtest_filter=${FILTER})
endfunction()

add_ethereum_test(FORK frontier)
add_ethereum_test(FORK homestead)
add_ethereum_test(FORK eip158)
add_ethereum_test(FORK eip150)
add_ethereum_test(FORK byzantium)
add_ethereum_test(FORK constantinoplefix)
add_ethereum_test(FORK istanbul)
add_ethereum_test(FORK berlin)
add_ethereum_test(FORK london)
add_ethereum_test(FORK paris)
add_ethereum_test(FORK shanghai)
add_ethereum_test(FORK cancun)
add_ethereum_test(FORK prague)
add_ethereum_test(FORK osaka)
