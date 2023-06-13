enable_testing()

find_package(GTest REQUIRED)
include(GoogleTest)

function(add_unit_test)
    set(OPTIONAL_ARGS ENABLE_LOGGING)
    set(ONE_VALUE_ARGS TARGET)
    set(MULTI_VALUE_ARGS SOURCES LIBRARIES)
    cmake_parse_arguments(ADD_UNIT_TEST "${OPTIONAL_ARGS}" "${ONE_VALUE_ARGS}" "${MULTI_VALUE_ARGS}" ${ARGN})

    add_executable(${ADD_UNIT_TEST_TARGET} ${ADD_UNIT_TEST_SOURCES})
    monad_compile_options(${ADD_UNIT_TEST_TARGET})

    if ("${ADD_UNIT_TEST_ENABLE_LOGGING}" STREQUAL "FALSE")
        target_compile_definitions(${ADD_UNIT_TEST_TARGET} PUBLIC DISABLE_LOGGING)
    endif()

    target_link_libraries(${ADD_UNIT_TEST_TARGET}
        GTest::GTest
        monad_unit_test_common
        ${ADD_UNIT_TEST_LIBRARIES}
    )
    gtest_discover_tests(${ADD_UNIT_TEST_TARGET})
endfunction()
