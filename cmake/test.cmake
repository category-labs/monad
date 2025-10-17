enable_testing()

include(FetchContent)

FetchContent_Declare(
  googletest
  URL https://github.com/google/googletest/archive/refs/tags/v1.14.0.tar.gz)

set(gtest_force_shared_crt OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)
list(APPEND CMAKE_PREFIX_PATH "${googletest_SOURCE_DIR}" "${googletest_BINARY_DIR}")
include_directories(
  SYSTEM
    "${googletest_SOURCE_DIR}/googletest/include"
    "${googletest_SOURCE_DIR}/googlemock/include")

include(GoogleTest)

function(add_unit_test)
  set(ONE_VALUE_ARGS TARGET)
  set(MULTI_VALUE_ARGS SOURCES LIBRARIES)
  cmake_parse_arguments(ADD_UNIT_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(
    ${ADD_UNIT_TEST_TARGET}
    ${ADD_UNIT_TEST_SOURCES}
    ${CMAKE_CURRENT_FUNCTION_LIST_DIR}/../test/unit/common/src/test/main.cpp)
  monad_compile_options(${ADD_UNIT_TEST_TARGET})

  target_link_libraries(
    ${ADD_UNIT_TEST_TARGET}
    PUBLIC GTest::gtest GTest::gmock monad_unit_test_common
           ${ADD_UNIT_TEST_LIBRARIES})
  gtest_discover_tests(${ADD_UNIT_TEST_TARGET})
endfunction()

function(add_integration_test)
  set(ONE_VALUE_ARGS TARGET)
  cmake_parse_arguments(ADD_INT_TEST "" "${ONE_VALUE_ARGS}" "" ${ARGN})

  add_unit_test(${ADD_INT_TEST_TARGET} ${ARGN})
  target_link_libraries(${ADD_INT_TEST_TARGET} PUBLIC monad_execution)

  if(NOT TARGET integration_tests)
    add_custom_target(integration_tests)
  endif()
  add_dependencies(integration_tests ${ADD_INT_TEST_TARGET})
endfunction()
