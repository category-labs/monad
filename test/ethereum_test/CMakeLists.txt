add_executable(monad-ethereum-test)
target_link_libraries(monad-ethereum-test PRIVATE nlohmann_json::nlohmann_json
                                                  monad GTest::gtest)
target_sources(
  monad-ethereum-test
  PRIVATE include/blockchain_test.hpp
          include/ethereum_test.hpp
          include/from_json.hpp
          include/general_state_test.hpp
          include/general_state_test_types.hpp
          src/blockchain_test.cpp
          src/ethereum_test.cpp
          src/general_state_test.cpp
          src/main.cpp)

target_include_directories(
  monad-ethereum-test PUBLIC ${PROJECT_SOURCE_DIR}/test/ethereum_test/include)
target_include_directories(
  monad-ethereum-test PUBLIC ${PROJECT_SOURCE_DIR}/test/unit/common/include)
monad_compile_options(monad-ethereum-test)

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
                   --gtest_filter=${FILTER})
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
add_ethereum_test(FORK merge)
add_ethereum_test(FORK shanghai)
