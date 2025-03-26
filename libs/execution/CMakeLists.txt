cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_execution)

# ##############################################################################
# deps
# ##############################################################################

# ##############################################################################
# libs
# ##############################################################################

add_library(
  monad_execution STATIC
  # chain
  "src/monad/chain/chain_config.h"
  "src/monad/chain/chain.cpp"
  "src/monad/chain/chain.hpp"
  "src/monad/chain/ethereum_mainnet.cpp"
  "src/monad/chain/ethereum_mainnet.hpp"
  "src/monad/chain/monad_chain.cpp"
  "src/monad/chain/monad_chain.hpp"
  "src/monad/chain/monad_devnet.cpp"
  "src/monad/chain/monad_devnet.hpp"
  "src/monad/chain/monad_mainnet.cpp"
  "src/monad/chain/monad_mainnet.hpp"
  "src/monad/chain/monad_revision.h"
  "src/monad/chain/monad_testnet.cpp"
  "src/monad/chain/monad_testnet.hpp"
  # core
  "src/monad/core/account.hpp"
  "src/monad/core/address.cpp"
  "src/monad/core/address.hpp"
  "src/monad/core/block.hpp"
  "src/monad/core/bytes.hpp"
  "src/monad/core/monad_block.hpp"
  "src/monad/core/fmt/account_fmt.hpp"
  "src/monad/core/fmt/address_fmt.hpp"
  "src/monad/core/fmt/block_fmt.hpp"
  "src/monad/core/fmt/bytes_fmt.hpp"
  "src/monad/core/fmt/int_fmt.hpp"
  "src/monad/core/fmt/receipt_fmt.hpp"
  "src/monad/core/fmt/signature_fmt.hpp"
  "src/monad/core/fmt/transaction_fmt.hpp"
  "src/monad/core/fmt/withdrawal_fmt.hpp"
  "src/monad/core/int.hpp"
  "src/monad/core/log_level_map.hpp"
  "src/monad/core/receipt.cpp"
  "src/monad/core/receipt.hpp"
  "src/monad/core/rlp/account_rlp.cpp"
  "src/monad/core/rlp/account_rlp.hpp"
  "src/monad/core/rlp/address_rlp.hpp"
  "src/monad/core/rlp/block_rlp.cpp"
  "src/monad/core/rlp/block_rlp.hpp"
  "src/monad/core/rlp/bytes_rlp.hpp"
  "src/monad/core/rlp/int_rlp.hpp"
  "src/monad/core/rlp/monad_block_rlp.cpp"
  "src/monad/core/rlp/monad_block_rlp.hpp"
  "src/monad/core/rlp/receipt_rlp.cpp"
  "src/monad/core/rlp/receipt_rlp.hpp"
  "src/monad/core/rlp/signature_rlp.cpp"
  "src/monad/core/rlp/signature_rlp.hpp"
  "src/monad/core/rlp/transaction_rlp.cpp"
  "src/monad/core/rlp/transaction_rlp.hpp"
  "src/monad/core/rlp/withdrawal_rlp.cpp"
  "src/monad/core/rlp/withdrawal_rlp.hpp"
  "src/monad/core/signature.cpp"
  "src/monad/core/signature.hpp"
  "src/monad/core/transaction.cpp"
  "src/monad/core/transaction.hpp"
  "src/monad/core/variant.hpp"
  "src/monad/core/withdrawal.hpp"
  # db
  "src/monad/db/block_db.cpp"
  "src/monad/db/block_db.hpp"
  "src/monad/db/db.hpp"
  "src/monad/db/db_cache.hpp"
  "src/monad/db/db_snapshot.cpp"
  "src/monad/db/db_snapshot.h"
  "src/monad/db/db_snapshot_filesystem.cpp"
  "src/monad/db/db_snapshot_filesystem.h"
  "src/monad/db/file_db.cpp"
  "src/monad/db/file_db.hpp"
  "src/monad/db/trie_db.cpp"
  "src/monad/db/trie_db.hpp"
  "src/monad/db/trie_rodb.hpp"
  "src/monad/db/util.cpp"
  "src/monad/db/util.hpp"
  # contract
  "src/monad/contract/mapping.hpp"
  "src/monad/contract/storage_adapter.hpp"
  "src/monad/contract/storage_array.hpp"
  "src/monad/contract/storage_variable.hpp"
  # execution
  "src/monad/execution/block_hash_buffer.cpp"
  "src/monad/execution/block_hash_buffer.hpp"
  "src/monad/execution/block_reward.cpp"
  "src/monad/execution/block_reward.hpp"
  "src/monad/execution/create_contract_address.cpp"
  "src/monad/execution/create_contract_address.hpp"
  "src/monad/execution/ethereum/dao.hpp"
  "src/monad/execution/evm.cpp"
  "src/monad/execution/evm.hpp"
  "src/monad/execution/evmc_host.cpp"
  "src/monad/execution/evmc_host.hpp"
  "src/monad/execution/execute_block.cpp"
  "src/monad/execution/execute_block.hpp"
  "src/monad/execution/execute_transaction.cpp"
  "src/monad/execution/execute_transaction.hpp"
  "src/monad/execution/explicit_evmc_revision.hpp"
  "src/monad/execution/fmt/event_trace_fmt.hpp"
  "src/monad/execution/genesis.hpp"
  "src/monad/execution/precompiles.cpp"
  "src/monad/execution/precompiles.hpp"
  "src/monad/execution/staking/bls.hpp"
  "src/monad/execution/staking/secp256k1.hpp"
  "src/monad/execution/staking/validator.hpp"
  "src/monad/execution/stateful_precompiles.cpp"
  "src/monad/execution/stateful_precompiles.hpp"
  "src/monad/execution/switch_evmc_revision.hpp"
  "src/monad/execution/trace/call_frame.cpp"
  "src/monad/execution/trace/call_frame.hpp"
  "src/monad/execution/trace/call_tracer.cpp"
  "src/monad/execution/trace/call_tracer.hpp"
  "src/monad/execution/trace/event_trace.cpp"
  "src/monad/execution/trace/event_trace.hpp"
  "src/monad/execution/trace/rlp/call_frame_rlp.cpp"
  "src/monad/execution/trace/rlp/call_frame_rlp.hpp"
  "src/monad/execution/transaction_gas.cpp"
  "src/monad/execution/transaction_gas.hpp"
  "src/monad/execution/tx_context.cpp"
  "src/monad/execution/tx_context.hpp"
  "src/monad/execution/validate_block.cpp"
  "src/monad/execution/validate_block.hpp"
  "src/monad/execution/validate_transaction.cpp"
  "src/monad/execution/validate_transaction.hpp"
  "src/monad/execution/wal_reader.cpp"
  "src/monad/execution/wal_reader.hpp"
  # rlp
  "src/monad/rlp/config.hpp"
  "src/monad/rlp/decode.hpp"
  "src/monad/rlp/decode_error.cpp"
  "src/monad/rlp/decode_error.hpp"
  "src/monad/rlp/encode2.hpp"
  # state
  "src/monad/state2/block_state.cpp"
  "src/monad/state2/block_state.hpp"
  "src/monad/state2/fmt/state_deltas_fmt.hpp"
  "src/monad/state2/proposal_state.hpp"
  "src/monad/state2/state_deltas.hpp"
  # state 3
  "src/monad/state3/account_state.cpp"
  "src/monad/state3/account_state.hpp"
  "src/monad/state3/account_substate.hpp"
  "src/monad/state3/state.cpp"
  "src/monad/state3/state.hpp"
  "src/monad/state3/version_stack.hpp"
  # types
  "src/monad/types/incarnation.hpp"
  # types/fmt
  "src/monad/types/fmt/incarnation_fmt.hpp")

target_include_directories(
  monad_execution
  PUBLIC ${PROJECT_SOURCE_DIR}/src
  PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/test
  PRIVATE ${Boost_INCLUDE_DIRS}
  PUBLIC ${silkpre_SOURCE_DIR}/lib)

target_link_libraries(
  monad_execution
  PUBLIC monad-compiler-vm
  PUBLIC monad_core
  PUBLIC monad_trie
  PRIVATE Boost::fiber
  PRIVATE Boost::json
  PRIVATE PkgConfig::brotli
  PUBLIC ethash::keccak
  PUBLIC evmc
  PUBLIC intx::intx
  PUBLIC nlohmann_json::nlohmann_json
  PUBLIC quill::quill
  PUBLIC silkpre
  PUBLIC unordered_dense
  PUBLIC TBB::tbb
  PUBLIC blst::blst)
monad_compile_options(monad_execution)

target_link_options(monad_execution PRIVATE LINKER:-z,defs)

# ##############################################################################
# unit tests
# ##############################################################################

monad_add_test_folder("src/monad/contract")
monad_add_test_folder("src/monad/core")
monad_add_test_folder("src/monad/db")
monad_add_test_folder("src/monad/execution")
monad_add_test_folder("src/monad/rlp")
monad_add_test_folder("src/monad/state2")
monad_add_test_folder("src/monad/trie")
