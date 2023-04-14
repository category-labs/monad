cmake_minimum_required(VERSION 3.20)

include(third_party/evmone/cmake/cable/bootstrap.cmake)
include(CableBuildInfo)

project(monad)

option(ASAN  "Turn on Address Sanitizer")
option(UBSAN "Turn on Undefined Behavior Sanitizer")

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

find_package(Boost REQUIRED COMPONENTS fiber log)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)
find_package(tl-expected REQUIRED)
find_package(tl-optional REQUIRED)

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
    target_compile_options(${target} PRIVATE -Wall -Wextra -Werror -Wconversion -Wpedantic)
endfunction()


############
### unit tests
############

add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/core/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/rlp/test)


############
### libs
############

# monad

add_library(monad STATIC

    ${PROJECT_SOURCE_DIR}/include/monad/config.hpp

    # core
    ${PROJECT_SOURCE_DIR}/include/monad/core/address.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/assert.h
    ${PROJECT_SOURCE_DIR}/include/monad/core/byte_string.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/bytes.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/core/concepts.hpp
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
    ${PROJECT_SOURCE_DIR}/include/monad/db/state_db.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/file_db.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/state_db.cpp

    # execution
    ${PROJECT_SOURCE_DIR}/include/monad/execution/config.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/create_contract_address.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/fork_traits.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/evm.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/evmc_host.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/static_precompiles.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/execution_model.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/transaction_processor.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/transaction_processor_data.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/execution/create_contract_address.cpp

    # fiber
    ${PROJECT_SOURCE_DIR}/include/monad/fiber/algorithm.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/fiber/properties.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/fiber/algorithm.cpp

    # rlp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/decode.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/decode_helpers.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/encode.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/encode_helpers.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/util.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/rlp/decode_helpers.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/rlp/encode_helpers.cpp
)
target_include_directories(monad
    PUBLIC ${PROJECT_SOURCE_DIR}/include
    PRIVATE ${Boost_INCLUDE_DIRS}
)
target_link_libraries(monad
    PRIVATE Boost::fiber
    PRIVATE Boost::log
    PRIVATE PkgConfig::brotli
    PRIVATE RocksDB::RocksDB

    PUBLIC ethash::keccak
    PUBLIC evmc
    PUBLIC intx::intx
    PUBLIC tl::expected
    PUBLIC tl::optional
)
monad_compile_options(monad)

if(ASAN)
  message("Address Sanitizer: On")
  target_compile_options(monad PUBLIC "-fsanitize=address" "-fno-omit-frame-pointer")
  target_link_options(monad PUBLIC "-fsanitize=address")
elseif(UBSAN)
  message("Undefined Behavior Sanitizer: On")
  target_compile_options(monad PUBLIC "-fsanitize=undefined" "-fno-omit-frame-pointer")
  target_link_options(monad PUBLIC "-fsanitize=undefined")
else()
  target_link_options(monad PRIVATE LINKER:-z,defs)
endif()

