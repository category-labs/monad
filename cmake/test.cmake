enable_testing()

find_package(GTest REQUIRED)
include(GoogleTest)

function(add_unit_test)
    set(MULTI_VALUE_ARGS SOURCES LIBRARIES)
    cmake_parse_arguments(ADD_UNIT_TEST "" "TARGET" "${MULTI_VALUE_ARGS}" ${ARGN})

    add_executable(${ADD_UNIT_TEST_TARGET} ${ADD_UNIT_TEST_SOURCES})
    monad_compile_options(${ADD_UNIT_TEST_TARGET})
    target_link_libraries(${ADD_UNIT_TEST_TARGET}
        GTest::GTest
        GTest::Main
        ${ADD_UNIT_TEST_LIBRARIES}
    )
    gtest_discover_tests(${ADD_UNIT_TEST_TARGET})
endfunction()
