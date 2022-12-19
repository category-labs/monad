cmake_minimum_required(VERSION 3.20)

include(third_party/evmone/cmake/cable/bootstrap.cmake)
include(CableBuildInfo)

include(tmpsrc/bootstrap.cmake)

project(monad)

############
### deps
############

find_package(Boost REQUIRED)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)

set(BUILD_SHARED_LIBS OFF)

add_subdirectory(third_party/ethash)
add_subdirectory(third_party/evmone)
add_subdirectory(third_party/intx)

include(cmake/Test.cmake)
include(cmake/Util.cmake)

############
### unit tests
############

add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/rlp/test)

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
    ${PROJECT_SOURCE_DIR}/include/monad/core/size_of.hpp
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
    PRIVATE PkgConfig::brotli
    PRIVATE rocksdb  # TODO pkgconfig

    PUBLIC evmc
    PUBLIC intx::intx
)
target_link_options(monad
    PRIVATE LINKER:-z,defs
)
monad_compile_options(monad)

# rlp
add_library(rlp STATIC
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/rlp.hpp
)

target_link_libraries(rlp PUBLIC monad)

include(tmpsrc/CMakeLists.txt)
