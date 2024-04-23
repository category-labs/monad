cmake_minimum_required(VERSION 3.20)

project(monad)

option(ASAN "Turn on Address Sanitizer")
option(UBSAN "Turn on Undefined Behavior Sanitizer")
option(EVMONE_TRACING
       "Enable instruction-level tracing for the evmone interpreter" OFF)
option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include(cmake/test.cmake)

# ##############################################################################
# deps
# ##############################################################################

add_subdirectory("monad-core")
add_subdirectory("monad-trie")

find_package(Boost REQUIRED COMPONENTS fiber graph json)
find_package(PkgConfig REQUIRED)
find_package(absl REQUIRED)
pkg_check_modules(brotli REQUIRED IMPORTED_TARGET libbrotlienc libbrotlidec)

# evmone
set(BUILD_SHARED_LIBS OFF)
add_subdirectory(third_party/evmone)
# always compile baseline with optimization due to stack size of dispatch_cgoto
set_source_files_properties(
  third_party/evmone/lib/evmone/baseline.cpp TARGET_DIRECTORY evmone
  PROPERTIES COMPILE_OPTIONS -O2)

# intx
add_subdirectory(third_party/intx)

# silkpre
set(OPTIONAL_BUILD_TESTS OFF)
add_subdirectory(third_party/silkpre)

# tbb
find_package(TBB REQUIRED)

function(monad_compile_options target)
  set_property(TARGET ${target} PROPERTY C_STANDARD 23)
  set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)

  target_compile_options(${target} PRIVATE -Wall -Wextra -Wpedantic
                                           -Wconversion -Werror)

  target_compile_options(
    ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)

  target_compile_definitions(${target} PUBLIC QUILL_ROOT_LOGGER_ONLY)

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

  target_compile_definitions(${target} PUBLIC "ENABLE_TRACING")

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
  "c++/monad/config.hpp"
  # analysis
  "c++/monad/analysis/analysis.cpp"
  "c++/monad/analysis/analysis.hpp"
  # cache
  "c++/monad/cache/account_storage_cache.hpp"
  # chain
  "c++/monad/chain/chain.cpp"
  "c++/monad/chain/chain.hpp"
  "c++/monad/chain/ethereum_mainnet.cpp"
  "c++/monad/chain/ethereum_mainnet.hpp"
  # core
  "c++/monad/core/account.hpp"
  "c++/monad/core/address.hpp"
  "c++/monad/core/block.hpp"
  "c++/monad/core/byte_string.hpp"
  "c++/monad/core/bytes.hpp"
  "c++/monad/core/fmt/account_fmt.hpp"
  "c++/monad/core/fmt/address_fmt.hpp"
  "c++/monad/core/fmt/block_fmt.hpp"
  "c++/monad/core/fmt/bytes_fmt.hpp"
  "c++/monad/core/fmt/int_fmt.hpp"
  "c++/monad/core/fmt/receipt_fmt.hpp"
  "c++/monad/core/fmt/transaction_fmt.hpp"
  "c++/monad/core/fmt/withdrawal_fmt.hpp"
  "c++/monad/core/int.hpp"
  "c++/monad/core/log_level_map.hpp"
  "c++/monad/core/receipt.cpp"
  "c++/monad/core/receipt.hpp"
  "c++/monad/core/rlp/account_rlp.cpp"
  "c++/monad/core/rlp/account_rlp.hpp"
  "c++/monad/core/rlp/address_rlp.hpp"
  "c++/monad/core/rlp/block_rlp.cpp"
  "c++/monad/core/rlp/block_rlp.hpp"
  "c++/monad/core/rlp/bytes_rlp.hpp"
  "c++/monad/core/rlp/int_rlp.hpp"
  "c++/monad/core/rlp/receipt_rlp.cpp"
  "c++/monad/core/rlp/receipt_rlp.hpp"
  "c++/monad/core/rlp/signature_rlp.cpp"
  "c++/monad/core/rlp/signature_rlp.hpp"
  "c++/monad/core/rlp/transaction_rlp.cpp"
  "c++/monad/core/rlp/transaction_rlp.hpp"
  "c++/monad/core/rlp/withdrawal_rlp.cpp"
  "c++/monad/core/rlp/withdrawal_rlp.hpp"
  "c++/monad/core/signature.cpp"
  "c++/monad/core/signature.hpp"
  "c++/monad/core/transaction.cpp"
  "c++/monad/core/transaction.hpp"
  "c++/monad/core/variant.hpp"
  "c++/monad/core/withdrawal.hpp"
  # db
  "c++/monad/db/block_db.cpp"
  "c++/monad/db/block_db.hpp"
  "c++/monad/db/db.hpp"
  "c++/monad/db/db_cache.hpp"
  "c++/monad/db/file_db.cpp"
  "c++/monad/db/file_db.hpp"
  "c++/monad/db/trie_db.cpp"
  "c++/monad/db/trie_db.hpp"
  "c++/monad/db/util.cpp"
  "c++/monad/db/util.hpp"
  # execution
  "c++/monad/execution/baseline_execute.cpp"
  "c++/monad/execution/baseline_execute.hpp"
  "c++/monad/execution/block_hash_buffer.cpp"
  "c++/monad/execution/block_hash_buffer.hpp"
  "c++/monad/execution/block_reward.cpp"
  "c++/monad/execution/block_reward.hpp"
  "c++/monad/execution/code_analysis.hpp"
  "c++/monad/execution/create_contract_address.cpp"
  "c++/monad/execution/create_contract_address.hpp"
  "c++/monad/execution/ethereum/dao.hpp"
  "c++/monad/execution/evm.cpp"
  "c++/monad/execution/evm.hpp"
  "c++/monad/execution/evmc_host.cpp"
  "c++/monad/execution/evmc_host.hpp"
  "c++/monad/execution/execute_block.cpp"
  "c++/monad/execution/execute_block.hpp"
  "c++/monad/execution/execute_transaction.cpp"
  "c++/monad/execution/execute_transaction.hpp"
  "c++/monad/execution/explicit_evmc_revision.hpp"
  "c++/monad/execution/fmt/trace_fmt.hpp"
  "c++/monad/execution/genesis.hpp"
  "c++/monad/execution/precompiles.cpp"
  "c++/monad/execution/precompiles.hpp"
  "c++/monad/execution/replay_block_db.hpp"
  "c++/monad/execution/trace.cpp"
  "c++/monad/execution/trace.hpp"
  "c++/monad/execution/transaction_gas.cpp"
  "c++/monad/execution/transaction_gas.hpp"
  "c++/monad/execution/tx_context.cpp"
  "c++/monad/execution/tx_context.hpp"
  "c++/monad/execution/validate_block.cpp"
  "c++/monad/execution/validate_block.hpp"
  "c++/monad/execution/validate_transaction.cpp"
  "c++/monad/execution/validate_transaction.hpp"
  # rlp
  "c++/monad/rlp/config.hpp"
  "c++/monad/rlp/decode.hpp"
  "c++/monad/rlp/decode_error.cpp"
  "c++/monad/rlp/decode_error.hpp"
  "c++/monad/rlp/encode2.hpp"
  # state
  "c++/monad/state2/block_state.cpp"
  "c++/monad/state2/block_state.hpp"
  "c++/monad/state2/fmt/state_deltas_fmt.hpp"
  "c++/monad/state2/state_deltas.hpp"
  # state 3
  "c++/monad/state3/account_state.cpp"
  "c++/monad/state3/account_state.hpp"
  "c++/monad/state3/account_substate.hpp"
  "c++/monad/state3/state.cpp"
  "c++/monad/state3/state.hpp"
  "c++/monad/state3/version_stack.hpp")

target_include_directories(
  monad
  PUBLIC ${PROJECT_SOURCE_DIR}/c++
  PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/test
  PRIVATE ${Boost_INCLUDE_DIRS}
  PUBLIC ${silkpre_SOURCE_DIR}/lib
  PUBLIC ${PROJECT_SOURCE_DIR}/third_party/komihash
  PUBLIC ${PROJECT_SOURCE_DIR}/third_party/thread-safe-lru)

set(TEST_DATA_DIR "${PROJECT_SOURCE_DIR}/test")
set(THIRD_PARTY_DIR "${PROJECT_SOURCE_DIR}/third_party")

configure_file(cmake/test_resource_data.h.in test/test_resource_data.h @ONLY)

target_link_libraries(
  monad
  PUBLIC monad_core
  PUBLIC monad_trie
  PRIVATE Boost::fiber
  PRIVATE Boost::graph
  PRIVATE Boost::json
  PRIVATE PkgConfig::brotli
  PRIVATE absl::btree
  PUBLIC ethash::keccak
  PUBLIC evmc
  PUBLIC evmone
  PUBLIC intx::intx
  PUBLIC nlohmann_json::nlohmann_json
  PUBLIC quill::quill
  PUBLIC silkpre
  PUBLIC unordered_dense
  PUBLIC TBB::tbb)
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
# cmds
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/cmd)

# ##############################################################################
# unit tests
# ##############################################################################

add_subdirectory(${PROJECT_SOURCE_DIR}/test/ethereum_test)
add_subdirectory(${PROJECT_SOURCE_DIR}/test/unit/common)
add_subdirectory(${PROJECT_SOURCE_DIR}/c++/monad/analysis)

function(monad_add_test2 target)
  add_executable(${target} "test/unit/common/src/test/main.cpp" ${ARGN})
  monad_compile_options(${target})
  target_compile_options(${target} PUBLIC "-Wno-missing-field-initializers"
  )# TODO
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

monad_add_test_folder("c++/monad/core")
monad_add_test_folder("c++/monad/db")
monad_add_test_folder("c++/monad/execution")
monad_add_test_folder("c++/monad/rlp")
monad_add_test_folder("c++/monad/state2")
monad_add_test_folder("c++/monad/trie")
