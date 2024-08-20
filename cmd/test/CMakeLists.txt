project(cmd)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

add_executable(cli_tool_test cli_tool_test.cpp ../cli_tool_impl.cpp)
monad_compile_options(cli_tool_test)
target_link_libraries(cli_tool_test PUBLIC monad_execution GTest::gtest_main PkgConfig::zstd PkgConfig::archive)
gtest_discover_tests(cli_tool_test)