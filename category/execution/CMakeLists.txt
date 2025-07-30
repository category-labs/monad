# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

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
  monad_execution_ethereum
  OBJECT
  # ethereum/chain
  "ethereum/chain/chain_config.h"
  "ethereum/chain/chain.cpp"
  "ethereum/chain/chain.hpp"
  "ethereum/chain/ethereum_mainnet.cpp"
  "ethereum/chain/ethereum_mainnet.hpp"
  "ethereum/chain/ethereum_mainnet_alloc.hpp"
  "ethereum/chain/genesis_state.cpp"
  "ethereum/chain/genesis_state.hpp"
  # ethereum/core
  "ethereum/core/account.hpp"
  "ethereum/core/address.hpp"
  "ethereum/core/base_ctypes.h"
  "ethereum/core/block.hpp"
  "ethereum/core/eth_ctypes.h"
  "ethereum/core/contract/big_endian.hpp"
  "ethereum/core/fmt/account_fmt.hpp"
  "ethereum/core/fmt/address_fmt.hpp"
  "ethereum/core/fmt/block_fmt.hpp"
  "ethereum/core/fmt/bytes_fmt.hpp"
  "ethereum/core/fmt/int_fmt.hpp"
  "ethereum/core/fmt/receipt_fmt.hpp"
  "ethereum/core/fmt/signature_fmt.hpp"
  "ethereum/core/fmt/transaction_fmt.hpp"
  "ethereum/core/fmt/withdrawal_fmt.hpp"
  "ethereum/core/log_level_map.hpp"
  "ethereum/core/receipt.cpp"
  "ethereum/core/receipt.hpp"
  "ethereum/core/rlp/account_rlp.cpp"
  "ethereum/core/rlp/account_rlp.hpp"
  "ethereum/core/rlp/address_rlp.hpp"
  "ethereum/core/rlp/block_rlp.cpp"
  "ethereum/core/rlp/block_rlp.hpp"
  "ethereum/core/rlp/bytes_rlp.hpp"
  "ethereum/core/rlp/int_rlp.hpp"
  "ethereum/core/rlp/receipt_rlp.cpp"
  "ethereum/core/rlp/receipt_rlp.hpp"
  "ethereum/core/rlp/signature_rlp.cpp"
  "ethereum/core/rlp/signature_rlp.hpp"
  "ethereum/core/rlp/transaction_rlp.cpp"
  "ethereum/core/rlp/transaction_rlp.hpp"
  "ethereum/core/rlp/withdrawal_rlp.cpp"
  "ethereum/core/rlp/withdrawal_rlp.hpp"
  "ethereum/core/signature.cpp"
  "ethereum/core/signature.hpp"
  "ethereum/core/transaction.cpp"
  "ethereum/core/transaction.hpp"
  "ethereum/core/variant.hpp"
  "ethereum/core/withdrawal.hpp"
  # ethereum/db
  "ethereum/db/block_db.cpp"
  "ethereum/db/block_db.hpp"
  "ethereum/db/db.hpp"
  "ethereum/db/db_cache.hpp"
  "ethereum/db/db_snapshot.cpp"
  "ethereum/db/db_snapshot.h"
  "ethereum/db/db_snapshot_filesystem.cpp"
  "ethereum/db/db_snapshot_filesystem.h"
  "ethereum/db/file_db.cpp"
  "ethereum/db/file_db.hpp"
  "ethereum/db/trie_db.cpp"
  "ethereum/db/trie_db.hpp"
  "ethereum/db/trie_rodb.hpp"
  "ethereum/db/util.cpp"
  "ethereum/db/util.hpp"
  # ethereum/event
  "ethereum/event/exec_event_ctypes.h"
  "ethereum/event/exec_event_ctypes_metadata.c"
  "ethereum/event/exec_event_recorder.cpp"
  "ethereum/event/exec_event_recorder.hpp"
  "ethereum/event/exec_iter_help.h"
  # ethereum/execution
  "ethereum/block_hash_buffer.cpp"
  "ethereum/block_hash_buffer.hpp"
  "ethereum/block_reward.cpp"
  "ethereum/block_reward.hpp"
  "ethereum/create_contract_address.cpp"
  "ethereum/create_contract_address.hpp"
  "ethereum/dao.hpp"
  "ethereum/evm.cpp"
  "ethereum/evm.hpp"
  "ethereum/evmc_host.cpp"
  "ethereum/evmc_host.hpp"
  "ethereum/execute_block.cpp"
  "ethereum/execute_block.hpp"
  "ethereum/execute_transaction.cpp"
  "ethereum/execute_transaction.hpp"
  "ethereum/explicit_evmc_revision.hpp"
  "ethereum/fmt/event_trace_fmt.hpp"
  "ethereum/precompiles.cpp"
  "ethereum/precompiles.hpp"
  "ethereum/precompiles_bls12.cpp"
  "ethereum/precompiles_bls12.hpp"
  "ethereum/precompiles_impl.cpp"
  "ethereum/switch_evmc_revision.hpp"
  "ethereum/trace/call_frame.cpp"
  "ethereum/trace/call_frame.hpp"
  "ethereum/trace/call_tracer.cpp"
  "ethereum/trace/call_tracer.hpp"
  "ethereum/trace/event_trace.cpp"
  "ethereum/trace/event_trace.hpp"
  "ethereum/trace/rlp/call_frame_rlp.cpp"
  "ethereum/trace/rlp/call_frame_rlp.hpp"
  "ethereum/transaction_gas.cpp"
  "ethereum/transaction_gas.hpp"
  "ethereum/tx_context.cpp"
  "ethereum/tx_context.hpp"
  "ethereum/validate_block.cpp"
  "ethereum/validate_block.hpp"
  "ethereum/validate_transaction.cpp"
  "ethereum/validate_transaction.hpp"
  # ethereum/metrics
  "ethereum/metrics/block_metrics.hpp"
  # ethereum/rlp
  "ethereum/rlp/config.hpp"
  "ethereum/rlp/decode.hpp"
  "ethereum/rlp/decode_error.cpp"
  "ethereum/rlp/decode_error.hpp"
  "ethereum/rlp/encode2.hpp"
  # ethereum/state2
  "ethereum/state2/block_state.cpp"
  "ethereum/state2/block_state.hpp"
  "ethereum/state2/fmt/state_deltas_fmt.hpp"
  "ethereum/state2/state_deltas.hpp"
  # ethereum/state3
  "ethereum/state3/account_state.cpp"
  "ethereum/state3/account_state.hpp"
  "ethereum/state3/account_substate.hpp"
  "ethereum/state3/state.cpp"
  "ethereum/state3/state.hpp"
  "ethereum/state3/version_stack.hpp"
  # ethereum/types
  "ethereum/types/incarnation.hpp"
  "ethereum/types/fmt/incarnation_fmt.hpp")

add_library(
  monad_execution_native
  OBJECT
  # monad/chain
  "monad/chain/monad_chain.cpp"
  "monad/chain/monad_chain.hpp"
  "monad/chain/monad_devnet.cpp"
  "monad/chain/monad_devnet.hpp"
  "monad/chain/monad_devnet_alloc.hpp"
  "monad/chain/monad_mainnet.cpp"
  "monad/chain/monad_mainnet.hpp"
  "monad/chain/monad_mainnet_alloc.hpp"
  "monad/chain/monad_revision.h"
  "monad/chain/monad_testnet.cpp"
  "monad/chain/monad_testnet.hpp"
  "monad/chain/monad_testnet_alloc.hpp"
  "monad/chain/monad_testnet2.cpp"
  "monad/chain/monad_testnet2.hpp"
  "monad/chain/monad_testnet2_alloc.hpp"
  # monad/core
  "monad/core/monad_block.hpp"
  "monad/core/rlp/monad_block_rlp.cpp"
  "monad/core/rlp/monad_block_rlp.hpp"
  # monad/execution
  "monad/validate_monad_block.cpp"
  "monad/validate_monad_block.hpp"
  # monad/state2
  "monad/state2/proposal_state.hpp")

target_include_directories(
  monad_execution_ethereum
  PUBLIC ${CATEGORY_MAIN_DIR}
  PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/test
  PRIVATE ${Boost_INCLUDE_DIRS}
  PUBLIC ${silkpre_SOURCE_DIR}/lib)

target_include_directories(
  monad_execution_native
  PUBLIC ${CATEGORY_MAIN_DIR}
  PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/test
  PRIVATE ${Boost_INCLUDE_DIRS})

target_link_libraries(
  monad_execution_ethereum
  PUBLIC monad-vm
  PUBLIC monad_core
  PUBLIC monad_trie
  PRIVATE blst::blst
  PRIVATE Boost::fiber
  PRIVATE Boost::json
  PUBLIC c-kzg-4844
  PRIVATE PkgConfig::brotli
  PUBLIC ethash::keccak
  PUBLIC evmc
  PUBLIC intx::intx
  PUBLIC nlohmann_json::nlohmann_json
  PUBLIC quill::quill
  PUBLIC silkpre
  PUBLIC unordered_dense
  PUBLIC TBB::tbb)
monad_compile_options(monad_execution_ethereum)

target_link_options(monad_execution_ethereum PRIVATE LINKER:-z,defs)

target_link_libraries(
  monad_execution_native
  PUBLIC monad_execution_ethereum
  PUBLIC monad_core
  PUBLIC monad_trie
  PUBLIC evmc
  PUBLIC intx::intx
  PUBLIC quill::quill)
monad_compile_options(monad_execution_native)

# ##############################################################################
# unit tests
# ##############################################################################

monad_add_test_folder("ethereum")
monad_add_test_folder("monad")
