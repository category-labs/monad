cmake_minimum_required(VERSION 3.20)

include(CTest)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(MONAD_COMPILER_TESTING)
    add_definitions(-DMONAD_COMPILER_TESTING)
endif()

add_subdirectory(libs/compiler)
add_subdirectory(libs/core)
add_subdirectory(libs/evm)
add_subdirectory(libs/fuzzing)
add_subdirectory(libs/interpreter)
if(MONAD_COMPILER_LLVM)
    add_subdirectory(libs/llvm)
endif()
add_subdirectory(libs/runtime)
add_subdirectory(libs/utils)
add_subdirectory(libs/vm)