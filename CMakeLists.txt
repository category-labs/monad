cmake_minimum_required(VERSION 3.20)

include(third_party/evmone/cmake/cable/bootstrap.cmake)
include(CableBuildInfo)

project(monad)

############
### deps
############

find_package(Boost REQUIRED)

add_subdirectory(third_party/ethash)
add_subdirectory(third_party/evmone)
add_subdirectory(third_party/intx)


############
### opts
############

function(monad_compile_options target)
    set_property(TARGET ${target} PROPERTY C_STANDARD 11)
    set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD 20)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)
    target_compile_options(${target} PRIVATE -Wall -Wextra -Werror)
endfunction()


############
### libs
############

# monad

add_library(monad STATIC
    # core
    ${PROJECT_SOURCE_DIR}/include/monad/core/assert.h
    ${PROJECT_SOURCE_DIR}/include/monad/core/byte_string.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/bytes.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/int.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/likely.h
    ${PROJECT_SOURCE_DIR}/src/monad/core/assert.c
    ${PROJECT_SOURCE_DIR}/src/monad/core/int.cpp

    # db
    ${PROJECT_SOURCE_DIR}/include/monad/db/file_db.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/file_db.cpp
)
target_include_directories(monad
    PUBLIC ${PROJECT_SOURCE_DIR}/include
    PRIVATE ${Boost_INCLUDE_DIRS}
)
target_link_libraries(monad
    PUBLIC evmc
    PUBLIC intx::intx
)
target_link_options(monad
    PRIVATE LINKER:-z,defs
)
monad_compile_options(monad)
