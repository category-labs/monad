include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(PkgConfig REQUIRED)

pkg_check_modules(archive REQUIRED IMPORTED_TARGET libarchive)
pkg_check_modules(cap REQUIRED IMPORTED_TARGET libcap)
pkg_check_modules(zstd REQUIRED IMPORTED_TARGET libzstd)

find_package(CLI11 REQUIRED)

add_executable(monad monad.cpp)
monad_compile_options(monad)

target_link_libraries(monad PRIVATE monad_execution monad_statesync
                                    CLI11::CLI11)

if(DEFINED ENV{GIT_COMMIT_HASH})
  set(GIT_COMMIT_HASH $ENV{GIT_COMMIT_HASH})
else()
  execute_process(
    COMMAND git rev-parse HEAD
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()

target_compile_definitions(monad PRIVATE GIT_COMMIT_HASH="${GIT_COMMIT_HASH}")
add_executable(monad_cli "cli_tool_main.cpp"
                         "cli_tool_impl.cpp")
monad_compile_options(monad_cli)
target_link_libraries(monad_cli PUBLIC monad_execution PkgConfig::archive PkgConfig::zstd CLI11::CLI11)

add_subdirectory(test)