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
add_subdirectory("monad-trie")

find_package(Boost REQUIRED COMPONENTS fiber graph log)
find_package(PkgConfig REQUIRED)
find_package(absl REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)
pkg_check_modules(rocksdb REQUIRED IMPORTED_TARGET rocksdb)

set(BUILD_SHARED_LIBS OFF)

add_subdirectory(third_party/evmone)
# always compile baseline with optimization due to stack size of dispatch_cgoto
set_source_files_properties(
  third_party/evmone/lib/evmone/baseline.cpp TARGET_DIRECTORY evmone
  PROPERTIES COMPILE_OPTIONS -O2)
add_subdirectory(third_party/intx)
add_subdirectory(third_party/silkpre)
add_subdirectory(third_party/quill SYSTEM)

function(monad_compile_options target)
  monad_core_compile_options(${target})

  target_compile_options(${target} PUBLIC -DQUILL_ROOT_LOGGER_ONLY)

  target_compile_options(
    ${target}
    PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-attributes=clang::no_sanitize>)

  # needed to resolve some potential false positives when compiling with
  # Boost.Graph
  target_compile_options(
    ${target} PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-maybe-uninitialized>)

  # this is needed to turn off ranges support in nlohmann_json, because the
  # ranges standard header triggers a clang bug which is fixed in trunk but not
  # currently available to us
  # https://gcc.gnu.org/bugzilla//show_bug.cgi?id=109647
  target_compile_definitions(${target} PUBLIC "JSON_HAS_RANGES=0")

  if(EVMONE_TRACING)
    target_compile_definitions(${target} PUBLIC EVMONE_TRACING=1)
  endif()
endfunction()

# ##############################################################################
# libs
# ##############################################################################

# monad

add_library(
  monad STATIC
  "include/monad/config.hpp"
  # analysis
  "include/monad/analysis/analysis.hpp"
  "src/monad/analysis/analysis.cpp"
  # core
  "include/monad/core/account_fmt.hpp"
  "include/monad/core/account_rlp.hpp"
  "include/monad/core/account.hpp"
  "include/monad/core/address_fmt.hpp"
  "include/monad/core/address_rlp.hpp"
  "include/monad/core/address.hpp"
  "include/monad/core/basic_formatter.hpp"
  "include/monad/core/block_fmt.hpp"
  "include/monad/core/block_rlp.hpp"
  "include/monad/core/block.hpp"
  "include/monad/core/byte_string.hpp"
  "include/monad/core/bytes_fmt.hpp"
  "include/monad/core/bytes_rlp.hpp"
  "include/monad/core/bytes.hpp"
  "include/monad/core/int_fmt.hpp"
  "include/monad/core/int_rlp.hpp"
  "include/monad/core/int.hpp"
  "include/monad/core/log_level_map.hpp"
  "include/monad/core/receipt_fmt.hpp"
  "include/monad/core/receipt_rlp.hpp"
  "include/monad/core/receipt.hpp"
  "include/monad/core/signature_rlp.hpp"
  "include/monad/core/signature.hpp"
  "include/monad/core/transaction_fmt.hpp"
  "include/monad/core/transaction_rlp.hpp"
  "include/monad/core/transaction.hpp"
  "include/monad/core/variant.hpp"
  "include/monad/core/withdrawal_rlp.hpp"
  "include/monad/core/withdrawal.hpp"
  "src/monad/core/account_rlp.cpp"
  "src/monad/core/block_rlp.cpp"
  "src/monad/core/receipt_rlp.cpp"
  "src/monad/core/receipt.cpp"
  "src/monad/core/signature_rlp.cpp"
  "src/monad/core/signature.cpp"
  "src/monad/core/transaction_rlp.cpp"
  "src/monad/core/transaction.cpp"
  "src/monad/core/withdrawal_rlp.cpp"
  # db
  "include/monad/db/assert.h"
  "include/monad/db/auto_detect_start_block_number.hpp"
  "include/monad/db/block_db.hpp"
  "include/monad/db/config.hpp"
  "include/monad/db/create_and_prune_block_history.hpp"
  "include/monad/db/db.hpp"
  "include/monad/db/file_db.hpp"
  "include/monad/db/in_memory_old_trie_db.hpp"
  "include/monad/db/in_memory_trie_db.hpp"
  "include/monad/db/permission.hpp"
  "include/monad/db/prepare_state.hpp"
  "include/monad/db/rocks_db_helper.hpp"
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
  "include/monad/execution/baseline_execute.hpp"
  "include/monad/execution/block_hash_buffer.hpp"
  "include/monad/execution/block_processor.hpp"
  "include/monad/execution/block_reward.hpp"
  "include/monad/execution/create_contract_address.hpp"
  "include/monad/execution/ethereum/dao.hpp"
  "include/monad/execution/ethereum/fork_traits.hpp"
  "include/monad/execution/evm.hpp"
  "include/monad/execution/evmc_host.hpp"
  "include/monad/execution/execute_transaction.hpp"
  "include/monad/execution/explicit_evmc_revision.hpp"
  "include/monad/execution/genesis.hpp"
  "include/monad/execution/precompiles.hpp"
  "include/monad/execution/replay_block_db.hpp"
  "include/monad/execution/transaction_gas.hpp"
  "include/monad/execution/tx_context.hpp"
  "include/monad/execution/validate_block.hpp"
  "include/monad/execution/validate_transaction.hpp"
  "include/monad/execution/validation_status.hpp"
  "src/monad/execution/baseline_execute.cpp"
  "src/monad/execution/block_hash_buffer.cpp"
  "src/monad/execution/block_processor.cpp"
  "src/monad/execution/block_reward.cpp"
  "src/monad/execution/create_contract_address.cpp"
  "src/monad/execution/evm.cpp"
  "src/monad/execution/evmc_host.cpp"
  "src/monad/execution/execute_transaction.cpp"
  "src/monad/execution/precompiles.cpp"
  "src/monad/execution/transaction_gas.cpp"
  "src/monad/execution/tx_context.cpp"
  "src/monad/execution/validate_transaction.cpp"
  # rlp
  "include/monad/rlp/decode.hpp"
  "include/monad/rlp/encode2.hpp"
  # state
  "include/monad/state2/block_state.hpp"
  "include/monad/state2/block_state_ops.hpp"
  "include/monad/state2/state_deltas_fmt.hpp"
  "include/monad/state2/state_deltas.hpp"
  "include/monad/state2/state.hpp"
  "include/monad/state2/substate.hpp"
  "src/monad/state2/block_state.cpp"
  "src/monad/state2/block_state_ops.cpp"
  "src/monad/state2/state_deltas.cpp"
  # trie
  "include/monad/trie/compact_encode.hpp"
  "include/monad/trie/nibbles_fmt.hpp"
  "include/monad/trie/nibbles_view.hpp"
  "include/monad/trie/nibbles.hpp"
  "include/monad/trie/node_rlp.hpp"
  "include/monad/trie/node.hpp"
  "include/monad/trie/trie.hpp"
  "include/monad/trie/rocks_cursor.hpp"
  "include/monad/trie/rocks_writer.hpp"
  "include/monad/trie/util.hpp"
  "include/monad/trie/key_buffer.hpp"
  "include/monad/trie/comparator.hpp"
  "include/monad/trie/rocks_comparator.hpp"
  "include/monad/trie/process_transformation_list.hpp"
  "include/monad/trie/update_fmt.hpp"
  "include/monad/trie/update.hpp"
  "include/monad/trie/get_trie_key_of_leaf.hpp"
  "src/monad/trie/node_rlp.cpp")

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
  PUBLIC monad_trie
  PRIVATE Boost::fiber
  PRIVATE Boost::graph
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

# ##############################################################################
# unit tests
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/test/ethereum_test)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common/src/test)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/analysis)
add_subdirectory(${PROJECT_SOURCE_DIR}/src/monad/execution/ethereum)

add_subdirectory(${PROJECT_SOURCE_DIR}/test/integration)

function(monad_add_test2 target)
  add_executable(${target} "test/unit/common/src/test/main.cpp" ${ARGN})
  monad_compile_options(${target})
  target_include_directories(${target} PRIVATE "test/unit/common/include")
  target_link_libraries(${target} monad GTest::GTest GTest::Main)
  gtest_discover_tests(${target} DISCOVERY_MODE PRE_TEST)
endfunction()

function(monad_add_test_folder target)
  file(GLOB_RECURSE test_files CONFIGURE_DEPENDS ${target}/test_*.cpp)
  foreach(test_file ${test_files})
    get_filename_component(test_name ${test_file} NAME_WLE)
    monad_add_test2(${test_name} ${test_file})
  endforeach()
endfunction()

monad_add_test_folder("src/monad/core")
monad_add_test_folder("src/monad/db")
monad_add_test_folder("src/monad/execution")
monad_add_test_folder("src/monad/rlp")
monad_add_test_folder("src/monad/state2")
monad_add_test_folder("src/monad/trie")

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
