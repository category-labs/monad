cmake_minimum_required(VERSION 3.20)

project(monad)

option(ASAN "Turn on Address Sanitizer")
option(UBSAN "Turn on Undefined Behavior Sanitizer")
option(EVMONE_TRACING
       "Enable instruction-level tracing for the evmone interpreter" OFF)

include(cmake/test.cmake)

# ##############################################################################
# deps
# ##############################################################################

add_subdirectory("monad-core")

find_package(Boost REQUIRED COMPONENTS fiber log)
find_package(PkgConfig REQUIRED)
find_package(absl REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)
pkg_check_modules(rocksdb REQUIRED IMPORTED_TARGET rocksdb)

set(BUILD_SHARED_LIBS OFF)

add_subdirectory(third_party/evmone)
add_subdirectory(third_party/intx)
add_subdirectory(third_party/silkpre)
add_subdirectory(third_party/quill SYSTEM)

function(monad_compile_options target)
  set_property(TARGET ${target} PROPERTY C_STANDARD 23)
  set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)
  target_compile_options(${target} PRIVATE -Wall -Wextra -Werror -Wconversion
                                           -Wpedantic)
  target_compile_options(
    ${target}
    PUBLIC $<$<CXX_COMPILER_ID:Clang>:-Wno-gnu-zero-variadic-macro-arguments>)
  target_compile_options(
    ${target} PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)
  if(EVMONE_TRACING)
    target_compile_definitions(${target} PRIVATE EVMONE_TRACING=1)
  endif()

  # this is needed to turn off ranges support in nlohmann_json, because the
  # ranges standard header triggers a clang bug which is fixed in trunk but not
  # currently available to us
  # https://gcc.gnu.org/bugzilla//show_bug.cgi?id=109647
  target_compile_definitions(${target} PUBLIC "JSON_HAS_RANGES=0")
endfunction()

# ##############################################################################
# unit tests
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/test/ethereum_test)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/core/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/db/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/ethereum)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/ethereum/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/rlp/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/state/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/trie/test)

add_subdirectory(${PROJECT_SOURCE_DIR}/test/integration)

# ##############################################################################
# fuzz tests
# ##############################################################################

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  if(MONAD_FUZZING)
    set(FUZZTEST_FUZZING_MODE
        ON
        CACHE INTERNAL "enable fuzzing" FORCE)
    add_subdirectory(${PROJECT_SOURCE_DIR}/test/fuzz)
  endif()
endif()

# ##############################################################################
# libs
# ##############################################################################

# monad

add_library(
  monad STATIC
  "include/monad/config.hpp"
  # core
  "include/monad/core/address.hpp"
  "include/monad/core/byte_string.hpp"
  "include/monad/core/bytes.hpp"
  "include/monad/core/concepts.hpp"
  "include/monad/core/int.hpp"
  "include/monad/core/variant.hpp"
  "include/monad/core/withdrawal.hpp"
  "src/monad/core/int.cpp"
  "src/monad/core/receipt.cpp"
  "src/monad/core/signature.cpp"
  "src/monad/core/transaction.cpp"
  # db
  "include/monad/db/assert.h"
  "include/monad/db/auto_detect_start_block_number.hpp"
  "include/monad/db/block_db.hpp"
  "include/monad/db/config.hpp"
  "include/monad/db/create_and_prune_block_history.hpp"
  "include/monad/db/db.hpp"
  "include/monad/db/file_db.hpp"
  "include/monad/db/in_memory_db.hpp"
  "include/monad/db/in_memory_trie_db.hpp"
  "include/monad/db/permission.hpp"
  "include/monad/db/prepare_state.hpp"
  "include/monad/db/rocks_db_helper.hpp"
  "include/monad/db/rocks_db.hpp"
  "include/monad/db/rocks_trie_db.hpp"
  "include/monad/db/state_db.hpp"
  "include/monad/db/trie_db_process_changes.hpp"
  "include/monad/db/trie_db_read_account.hpp"
  "include/monad/db/trie_db_read_storage.hpp"
  "include/monad/db/util.hpp"
  "src/monad/db/block_db.cpp"
  "src/monad/db/file_db.cpp"
  "src/monad/db/rocks_db_helper.cpp"
  "src/monad/db/state_db.cpp"
  # execution
  "include/monad/execution/config.hpp"
  "include/monad/execution/create_contract_address.hpp"
  "include/monad/execution/ethereum/fork_traits.hpp"
  "include/monad/execution/evm.hpp"
  "include/monad/execution/evmc_host.hpp"
  "include/monad/execution/evmone_baseline_interpreter.hpp"
  "include/monad/execution/ethereum/dao.hpp"
  "include/monad/execution/ethereum/genesis.hpp"
  "include/monad/execution/precompiles.hpp"
  "include/monad/execution/precompiles/elliptic_curve_recover.hpp"
  "include/monad/execution/precompiles/sha256_hash.hpp"
  "include/monad/execution/precompiles/ripemd160_hash.hpp"
  "include/monad/execution/precompiles/identity.hpp"
  "include/monad/execution/precompiles/modular_exponentiation.hpp"
  "include/monad/execution/precompiles/bn_add.hpp"
  "include/monad/execution/precompiles/bn_multiply.hpp"
  "include/monad/execution/precompiles/bn_pairing.hpp"
  "include/monad/execution/precompiles/blake2f.hpp"
  "include/monad/execution/execution_model.hpp"
  "include/monad/execution/replay_block_db.hpp"
  "include/monad/execution/transaction_processor.hpp"
  "include/monad/execution/transaction_processor_data.hpp"
  "src/monad/execution/create_contract_address.cpp"
  # fiber
  "include/monad/fiber/algorithm.hpp"
  "include/monad/fiber/properties.hpp"
  "src/monad/fiber/algorithm.cpp"
  # logging
  "include/monad/logging/config.hpp"
  "include/monad/logging/fake_logger.hpp"
  "include/monad/logging/fake_log_macros.hpp"
  "include/monad/logging/formatter.hpp"
  "include/monad/logging/monad_log.hpp"
  "include/monad/logging/quill_logger.hpp"
  "include/monad/logging/quill_log_macros.hpp"
  # rlp
  "include/monad/rlp/decode.hpp"
  "include/monad/rlp/decode_helpers.hpp"
  "include/monad/rlp/encode.hpp"
  "include/monad/rlp/encode_helpers.hpp"
  "include/monad/rlp/util.hpp"
  "src/monad/rlp/decode_helpers.cpp"
  "src/monad/rlp/encode_helpers.cpp"
  # state
  "include/monad/state2/state.hpp"
  "include/monad/state2/state_ops.hpp"
  "src/monad/state2/state.cpp"
  "src/monad/state2/state_ops.cpp"
  "include/monad/state/account_state.hpp"
  "include/monad/state/code_state.hpp"
  "include/monad/state/state.hpp"
  "include/monad/state/value_state.hpp"
  "include/monad/state/state_changes.hpp"
  # trie
  "include/monad/trie/compact_encode.hpp"
  "include/monad/trie/nibbles.hpp"
  "include/monad/trie/nibbles_view.hpp"
  "include/monad/trie/node.hpp"
  "include/monad/trie/trie.hpp"
  "include/monad/trie/rocks_cursor.hpp"
  "include/monad/trie/rocks_writer.hpp"
  "include/monad/trie/util.hpp"
  "include/monad/trie/key_buffer.hpp"
  "include/monad/trie/comparator.hpp"
  "include/monad/trie/rocks_comparator.hpp"
  "include/monad/trie/process_transformation_list.hpp"
  "include/monad/trie/update.hpp"
  "include/monad/trie/get_trie_key_of_leaf.hpp")

target_include_directories(
  monad
  PUBLIC ${PROJECT_SOURCE_DIR}/include
  PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/test
  PRIVATE ${Boost_INCLUDE_DIRS}
  PUBLIC ${silkpre_SOURCE_DIR}/lib)

set(TEST_DATA_DIR "${PROJECT_SOURCE_DIR}/test")
set(THIRD_PARTY_DIR "${PROJECT_SOURCE_DIR}/third_party")

configure_file(cmake/test_resource_data.h.in test/test_resource_data.h @ONLY)

target_link_libraries(
  monad
  PUBLIC monad_core
  PRIVATE Boost::fiber
  PRIVATE Boost::log
  PRIVATE PkgConfig::brotli
  PRIVATE PkgConfig::rocksdb
  PRIVATE absl::btree
  PUBLIC ethash::keccak
  PUBLIC evmc
  PUBLIC evmone
  PUBLIC intx::intx
  PUBLIC nlohmann_json::nlohmann_json
  PUBLIC quill::quill
  PUBLIC silkpre
  PUBLIC tl::expected
  PUBLIC tl::optional
  PUBLIC unordered_dense)
monad_compile_options(monad)

if(ASAN)
  message("Address Sanitizer: On")
  target_compile_options(monad PUBLIC "-fsanitize=address"
                                      "-fno-omit-frame-pointer")
  target_link_options(monad PUBLIC "-fsanitize=address")
endif()
if(UBSAN)
  message("Undefined Behavior Sanitizer: On")
  target_compile_options(monad PUBLIC "-fsanitize=undefined"
                                      "-fno-omit-frame-pointer" "-fPIC")
  target_link_options(monad PUBLIC "-fsanitize=undefined")
endif()
if(NOT UBSAN AND NOT ASAN)
  target_link_options(monad PRIVATE LINKER:-z,defs)
endif()
