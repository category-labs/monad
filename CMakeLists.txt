cmake_minimum_required(VERSION 3.20)

include(third_party/evmone/cmake/cable/bootstrap.cmake)
include(CableBuildInfo)

include(tmpsrc/bootstrap.cmake)

project(monad)

############
### conan
############

list(APPEND CMAKE_MODULE_PATH ${CMAKE_BINARY_DIR})
list(APPEND CMAKE_PREFIX_PATH ${CMAKE_BINARY_DIR})

include(${PROJECT_SOURCE_DIR}/conan/cmake-conan/conan.cmake)

conan_cmake_autodetect(settings)

conan_cmake_install(
    PATH_OR_REFERENCE ${PROJECT_SOURCE_DIR}/conan/conanfile.txt
    BUILD missing
    ENV CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER}
    SETTINGS ${settings}
)

find_package(RocksDB)


############
### deps
############

find_package(Boost REQUIRED COMPONENTS fiber)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)

set(BUILD_SHARED_LIBS OFF)
set(ETHASH_BUILD_TESTS OFF)

add_subdirectory(third_party/ethash)
add_subdirectory(third_party/evmone)
add_subdirectory(third_party/intx)

include(cmake/test.cmake)

function(monad_compile_options target)
    set_property(TARGET ${target} PROPERTY C_STANDARD 11)
    set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD 20)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)
    target_compile_options(${target} PRIVATE -Wall -Wextra -Werror)
endfunction()


############
### unit tests
############

add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/core/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/rlp/test)


############
### libs
############

# monad

add_library(monad STATIC
    # core
    ${PROJECT_SOURCE_DIR}/include/monad/core/address.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/assert.h
    ${PROJECT_SOURCE_DIR}/include/monad/core/byte_string.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/bytes.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/huge_mem.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/int.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/likely.h
    ${PROJECT_SOURCE_DIR}/include/monad/core/size_of.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/assert.c
    ${PROJECT_SOURCE_DIR}/src/monad/core/huge_mem.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/int.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/receipt.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/signature.cpp

    # db
    ${PROJECT_SOURCE_DIR}/include/monad/db/file_db.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/file_db.cpp

    # fiber
    ${PROJECT_SOURCE_DIR}/include/monad/fiber/algorithm.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/fiber/properties.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/fiber/algorithm.cpp

    # rlp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/encode.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/encode_helpers.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/util.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/rlp/encode_helpers.cpp
)
target_include_directories(monad
    PUBLIC ${PROJECT_SOURCE_DIR}/include
    PRIVATE ${Boost_INCLUDE_DIRS}
)
target_link_libraries(monad
    PRIVATE Boost::fiber
    PRIVATE PkgConfig::brotli
    PRIVATE RocksDB::RocksDB

    PUBLIC evmc
    PUBLIC intx::intx
)
target_link_options(monad
    PRIVATE LINKER:-z,defs
)
monad_compile_options(monad)

include(tmpsrc/CMakeLists.txt)
