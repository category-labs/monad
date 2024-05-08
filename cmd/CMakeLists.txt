include_directories(${CMAKE_CURRENT_SOURCE_DIR})

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
add_executable(interactive_cli interactive_cli_main.cpp)
monad_compile_options(interactive_cli)
target_link_libraries(interactive_cli PUBLIC monad_execution CLI11::CLI11)
