cmake_minimum_required(VERSION 3.20)

include(third_party/evmone/cmake/cable/bootstrap.cmake)
include(CableBuildInfo)

project(monad)

option(ASAN "Turn on Address Sanitizer")
option(UBSAN "Turn on Undefined Behavior Sanitizer")

include(cmake/test.cmake)

# ##############################################################################
# deps
# ##############################################################################

set(VCPKG_ROOT_DIR "${PROJECT_SOURCE_DIR}/third_party/vcpkg")

if(NOT CMAKE_TOOLCHAIN_FILE STREQUAL
   "${VCPKG_ROOT_DIR}/scripts/buildsystems/vcpkg.cmake"
)
    # This must be forced so dependency builds pick it up
    if(CMAKE_TOOLCHAIN_FILE)
        set(VCPKG_CHAINLOAD_TOOLCHAIN_FILE
            "${CMAKE_TOOLCHAIN_FILE}"
            CACHE INTERNAL "vcpkg chained toolchain file"
        )
    endif()
    set(CMAKE_TOOLCHAIN_FILE
        "${VCPKG_ROOT_DIR}/scripts/buildsystems/vcpkg.cmake"
        CACHE INTERNAL "vcpkg toolchain file" FORCE
    )
endif()
include(${VCPKG_ROOT_DIR}/scripts/buildsystems/vcpkg.cmake)

find_package(Boost REQUIRED COMPONENTS fiber log)
find_package(PkgConfig REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)
pkg_check_modules(rocksdb REQUIRED IMPORTED_TARGET rocksdb)
find_package(tl-expected REQUIRED)
find_package(tl-optional REQUIRED)
find_package(quill REQUIRED)

set(BUILD_SHARED_LIBS OFF)
set(ETHASH_BUILD_TESTS OFF)

add_subdirectory(third_party/ethash)
add_subdirectory(third_party/evmone)
add_subdirectory(third_party/intx)
add_subdirectory(third_party/silkpre)

function(monad_compile_options target)
    set_property(TARGET ${target} PROPERTY C_STANDARD 11)
    set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD 20)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)
    target_compile_options(
        ${target} PRIVATE -Wall -Wextra -Werror -Wconversion -Wpedantic
    )
    target_compile_options(
        ${target}
        PUBLIC
            $<$<CXX_COMPILER_ID:Clang>:-Wno-gnu-zero-variadic-macro-arguments>
    )
    target_compile_options(
        ${target}
        PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>
    )
endfunction()

# ##############################################################################
# unit tests
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/core/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/db/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/ethereum)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/ethereum/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/rlp/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/trie/test)

# ##############################################################################
# fuzz tests
# ##############################################################################

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    # only include if fuzzing mode is turned on
    if(FUZZTEST_FUZZING_MODE)
        # TODO: figure out why vcpkg is interferring with target names. Prior to
        # introducing vcpkg, there were no conflicts in target names. Post
        # vcpkg, we need the below workaround so that cmake is not adding
        # multiple GTest::gtest targets. Our workaround is to ask all
        # dependencies of fuzztest not to pull in and build their own gtest
        set(FUZZTEST_USE_GTEST OFF)
        set(FUZZTEST_TESTING OFF)
        set(ABSL_USE_EXTERNAL_GOOGLETEST ON)
        set(ANTLR_BUILD_CPP_TESTS OFF)

        add_subdirectory(${PROJECT_SOURCE_DIR}/third_party/fuzztest)
        add_subdirectory(${PROJECT_SOURCE_DIR}/test/fuzz)
    endif()
elseif(FUZZTEST_FUZZING_MODE)
    message(FATAL_ERROR "FATAL: FUZZTEST_FUZZING_MODE only valid with Clang")
endif()

# ##############################################################################
# libs
# ##############################################################################

# monad

add_library(
    monad STATIC
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
    ${PROJECT_SOURCE_DIR}/include/monad/core/variant.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/assert.c
    ${PROJECT_SOURCE_DIR}/src/monad/core/huge_mem.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/int.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/receipt.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/signature.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/core/transaction.cpp
    # db
    ${PROJECT_SOURCE_DIR}/include/monad/db/block_db.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/db/config.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/db/file_db.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/db/state_db.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/block_db.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/file_db.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/db/state_db.cpp
    ${PROJECT_SOURCE_DIR}/include/monad/db/trie_db.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/db/util.hpp
    # execution
    ${PROJECT_SOURCE_DIR}/include/monad/execution/config.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/create_contract_address.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/fork_traits.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/evm.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/evmc_host.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/config.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/elliptic_curve_recover.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/sha256_hash.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/ripemd160_hash.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/identity.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/modular_exponentiation.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/bn_add.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/bn_multiply.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/bn_pairing.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/ethereum/static_precompiles/blake2f.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/static_precompiles.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/execution_model.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/replay_block_db.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/transaction_processor.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/execution/transaction_processor_data.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/execution/create_contract_address.cpp
    # fiber
    ${PROJECT_SOURCE_DIR}/include/monad/fiber/algorithm.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/fiber/properties.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/fiber/algorithm.cpp
    # logging
    ${PROJECT_SOURCE_DIR}/include/monad/logging/config.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/logging/fake_logger.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/logging/fake_log_macros.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/logging/formatter.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/logging/monad_log.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/logging/quill_logger.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/logging/quill_log_macros.hpp
    # rlp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/decode.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/decode_helpers.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/encode.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/encode_helpers.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/rlp/util.hpp
    ${PROJECT_SOURCE_DIR}/src/monad/rlp/decode_helpers.cpp
    ${PROJECT_SOURCE_DIR}/src/monad/rlp/encode_helpers.cpp
    # trie
    ${PROJECT_SOURCE_DIR}/include/monad/trie/compact_encode.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/nibbles.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/nibbles_view.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/node.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/trie.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/rocks_cursor.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/rocks_writer.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/util.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/assert.h
    ${PROJECT_SOURCE_DIR}/include/monad/trie/key_buffer.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/comparator.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/rocks_comparator.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/process_transformation_list.hpp
    ${PROJECT_SOURCE_DIR}/include/monad/trie/update.hpp
)

target_include_directories(
    monad
    PUBLIC ${PROJECT_SOURCE_DIR}/include
    PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/test
    PRIVATE ${Boost_INCLUDE_DIRS}
    PUBLIC ${silkpre_SOURCE_DIR}/lib
)

set(TEST_DATA_DIR "${PROJECT_SOURCE_DIR}/test")

configure_file(cmake/test_resource_data.h.in test/test_resource_data.h @ONLY)

target_link_libraries(
    monad
    PRIVATE Boost::fiber
    PRIVATE Boost::log
    PRIVATE PkgConfig::brotli
    PRIVATE PkgConfig::rocksdb
    PUBLIC ethash::keccak
    PUBLIC evmc
    PUBLIC intx::intx
    PUBLIC tl::expected
    PUBLIC tl::optional
    PUBLIC quill::quill
    PUBLIC silkpre
)
monad_compile_options(monad)

if(ASAN)
    message("Address Sanitizer: On")
    target_compile_options(
        monad PUBLIC "-fsanitize=address" "-fno-omit-frame-pointer"
    )
    target_link_options(monad PUBLIC "-fsanitize=address")
elseif(UBSAN)
    message("Undefined Behavior Sanitizer: On")
    target_compile_options(
        monad PUBLIC "-fsanitize=undefined" "-fno-omit-frame-pointer"
    )
    target_link_options(monad PUBLIC "-fsanitize=undefined")
else()
    target_link_options(monad PRIVATE LINKER:-z,defs)
endif()
