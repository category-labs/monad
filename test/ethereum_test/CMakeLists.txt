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

ExternalProject_Add(
  MonadSpecTestFixtures
  URL "https://github.com/monad-developers/execution-specs/releases/download/tests-monad@v1.1.1/fixtures_monad.tar.gz"
  URL_HASH "SHA256=1837b6bbbb51bd956623c5efc92f0c6123be7ea7563492703ff085d7c31876f2"
  PREFIX ${CMAKE_BINARY_DIR}
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ""
  INSTALL_COMMAND ""
  LOG_DOWNLOAD ON)

ExternalProject_Add(
  MonadAmsterdamSpecTestFixtures
  URL "https://github.com/monad-developers/execution-specs/releases/download/tests-monad_amsterdam@v0.2.0/fixtures_monad_amsterdam.tar.gz"
  URL_HASH "SHA256=20b2a55f49a4b777f1abc6c196dc0afad22475b0ac598a39cc94fc598e22619d"
  PREFIX ${CMAKE_BINARY_DIR}
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ""
  INSTALL_COMMAND ""
  LOG_DOWNLOAD ON)

add_executable(monad-ethereum-test)
target_link_libraries(monad-ethereum-test PRIVATE GTest::gtest monad-test-utils)
target_sources(
  monad-ethereum-test
  PRIVATE include/blockchain_test.hpp
          include/event.hpp
          include/revision_map.hpp
          include/transaction_test.hpp
          src/blockchain_test.cpp
          src/event.cpp
          src/main.cpp
          src/transaction_test.cpp)

target_include_directories(
  monad-ethereum-test PUBLIC ${CATEGORY_MAIN_DIR})
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

function(add_monad_test)
  set(ONE_VALUE_ARGS FORK)
  cmake_parse_arguments(ADD_MONAD_TEST "" "${ONE_VALUE_ARGS}" "" ${ARGN})

  set(EXCLUSION_FILE
      "${CMAKE_CURRENT_SOURCE_DIR}/exclude/${ADD_MONAD_TEST_FORK}.cmake")
  include(${EXCLUSION_FILE})
  set(TESTS_EXCLUDED "${ADD_MONAD_TEST_FORK}_excluded_tests")

  list(JOIN ${TESTS_EXCLUDED} ":" TESTS_EXCLUDED)
  set(FILTER "-:${TESTS_EXCLUDED}")

  add_test(NAME ${ADD_MONAD_TEST_FORK}_monad_ethereum_test
           COMMAND monad-ethereum-test --fork ${ADD_MONAD_TEST_FORK}
                  # TODO: not ready yet
                  #  --record-exec-events
                   --blockchain-tests ${CMAKE_BINARY_DIR}/src/MonadSpecTestFixtures/blockchain_tests
                   --gtest_filter=${FILTER})
endfunction()

add_monad_test(FORK MONAD_EIGHT)
add_monad_test(FORK MONAD_NINE)
add_monad_test(FORK MONAD_NEXT)

# MONAD_NEXT Amsterdam spec tests, from a separate fixtures release. While the
# whole suite is excluded (see the exclusion file), the runner exits non-zero
# via its "No tests were run" guard, so the job is marked WILL_FAIL to keep
# ctest green. WILL_FAIL is set only while the suite is fully excluded: once
# individual tests are re-enabled by dropping entries from the exclusion list,
# the job runs normally so real failures (and unexpected passes) surface.
include(${CMAKE_CURRENT_SOURCE_DIR}/exclude/MONAD_NEXT_amsterdam.cmake)
list(JOIN MONAD_NEXT_amsterdam_excluded_tests ":" TESTS_EXCLUDED)
add_test(NAME MONAD_NEXT_amsterdam_monad_ethereum_test
         COMMAND monad-ethereum-test --fork MONAD_NEXT
                 --blockchain-tests ${CMAKE_BINARY_DIR}/src/MonadAmsterdamSpecTestFixtures/blockchain_tests
                 --gtest_filter=-:${TESTS_EXCLUDED})
if(MONAD_NEXT_amsterdam_excluded_tests STREQUAL "BlockchainTests.*")
  set_tests_properties(MONAD_NEXT_amsterdam_monad_ethereum_test
                       PROPERTIES WILL_FAIL TRUE)
endif()

add_ethereum_test(FORK istanbul)
add_ethereum_test(FORK berlin)
add_ethereum_test(FORK london)
add_ethereum_test(FORK paris)
add_ethereum_test(FORK shanghai)
add_ethereum_test(FORK cancun)
add_ethereum_test(FORK prague)
add_ethereum_test(FORK osaka)
