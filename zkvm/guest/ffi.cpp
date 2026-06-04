// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// Phase 4 — ingest a reth-format execution witness from the eth-act standard
// input interface, reconstruct the partial state trie, execute the embedded
// block sequentially via execute_block_zkvm<traits>, and emit the resulting
// post-state root as the 32-byte output.
//
// The Rust ZisK / SP1 guest crates link this library and call
// monad_zkvm_execute_witness from their respective entrypoints. The C++
// side owns input/output via the eth-act standard interface
// (zkvm/core/zkvm_io.h):
//   - read_input(...)  — fetches the RLP-encoded witness buffer
//   - write_output(...) — emits the computed post-state root as 32 bytes
// Both symbols are resolved by the backend's runtime (ziskos on ZisK; the
// SP1 program crate provides a thin shim that wraps sp1_zkvm::io; the x86
// test runner provides them against a --input file).

#include <zkvm/core/zkvm_io.h>
#include <zkvm/guest/execute_block_zkvm.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <cstddef>
#include <cstdint>

namespace
{
    // EVM-only dispatch wrapper: SWITCH_EVM_TRAITS forwards a runtime
    // `evmc_revision` to a function template parameter, so we need a
    // helper whose only template parameter is `traits` (the function
    // template the macro can name). ChainContext<traits> for EVM traits
    // is an empty aggregate, so we materialise it here.
    template <monad::Traits traits>
    monad::Result<monad::bytes32_t> dispatch(
        monad::Chain const &chain, monad::Block const &block,
        monad::PartialTrieDb &pdb, monad::vm::VM &vm,
        monad::BlockHashBuffer const &block_hash_buffer)
    {
        return monad::execute_block_zkvm<traits>(
            chain,
            block,
            pdb,
            vm,
            block_hash_buffer,
            monad::ChainContext<traits>{});
    }
}

extern "C" void monad_zkvm_execute_witness(void)
{
    // 1. Read + parse the witness.
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());

    // 2. Derive the pre-state root from the first node in the witness. The
    //    encoder emits the accounts-trie root (or its wrapping extension)
    //    as the first entry, so its keccak hash equals the live state root
    //    by construction. Empty witness ⇒ empty trie ⇒ NULL_ROOT.
    monad::bytes32_t pre_state_root = monad::NULL_ROOT;
    {
        monad::byte_string_view view = witness.value().encoded_nodes;
        if (!view.empty()) {
            auto const first = monad::rlp::parse_list_metadata_raw(view);
            MONAD_ASSERT(first.has_value());
            pre_state_root = monad::to_bytes(monad::keccak256(first.value()));
        }
    }

    // 3. Reconstruct the partial state trie from the pre-state.
    auto pdb_result = monad::PartialTrieDb::from_witness(
        pre_state_root,
        witness.value().encoded_nodes,
        witness.value().encoded_codes);
    MONAD_ASSERT(pdb_result.has_value());
    auto &pdb = pdb_result.value();

    // 4. Decode the embedded block.
    monad::byte_string_view block_view = witness.value().block_rlp;
    auto block_result = monad::rlp::decode_block(block_view);
    MONAD_ASSERT(block_result.has_value());
    MONAD_ASSERT(block_view.empty());
    auto const &block = block_result.value();

    // 5. Build the execution context. EthereumMainnet is the MVP chain;
    //    monad-chain dispatch lands when we wire monad witnesses up.
    //    BlockHashBuffer is left empty in Phase 4 — populating it from
    //    witness.encoded_headers is a follow-up; blocks that don't read
    //    the BLOCKHASH opcode are unaffected by this.
    monad::EthereumMainnet const chain;
    monad::vm::VM vm;
    monad::BlockHashBufferFinalized const block_hash_buffer;
    pdb.set_block_and_prefix(block.header.number);

    // 6. Pick the EVM revision from the block's position on the mainnet
    //    fork schedule and dispatch into the templated guest pipeline. The
    //    witness is assumed to carry a real Ethereum block, so its number
    //    and timestamp select the revision the same way the live node does.
    monad_eth_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);
    auto const root_result = [&]() -> monad::Result<monad::bytes32_t> {
        SWITCH_EVM_TRAITS(dispatch, chain, block, pdb, vm, block_hash_buffer);
        // SWITCH_EVM_TRAITS only covers Byzantium+; older revisions fall
        // through. execute_block_zkvm's static_assert requires
        // Spurious-Dragon+ anyway.
        return monad::BlockError::FieldBeforeFork;
    }();
    MONAD_ASSERT(root_result.has_value());

    monad::bytes32_t const &state_root = root_result.value();
    write_output(state_root.bytes, sizeof(state_root.bytes));
}
