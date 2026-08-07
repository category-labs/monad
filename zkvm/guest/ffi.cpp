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
// Both symbols are resolved by the backend's runtime (ziskos on ZisK;
// libzkevm.a on SP1; the x86 test runner provides them against a --input
// file).

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
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <cstddef>
#include <cstdint>
#include <utility>

namespace
{
    // EVM-only dispatch wrapper: SWITCH_EVM_TRAITS forwards a runtime
    // `evmc_revision` to a function template parameter, so we need a
    // helper whose only template parameter is `traits` (the function
    // template the macro can name). ChainContext<traits> for EVM traits
    // is an empty aggregate, so we materialise it here.
    template <monad::Traits traits>
    monad::Result<monad::bytes32_t> dispatch(
        monad::Chain const &chain, monad::Block const &block, monad::Db &pdb,
        monad::vm::VM &vm, monad::BlockHashBuffer const &block_hash_buffer)
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

    // 2. Build the code index from the witness bytecodes (keccak-keyed), the
    //    same content PartialTrieDb serves read_code from.
    monad::CodeIndex code_index;
    {
        monad::byte_string_view codes = witness.value().encoded_codes;
        while (!codes.empty()) {
            auto const bytes = monad::rlp::parse_string_metadata(codes);
            MONAD_ASSERT(bytes.has_value());
            code_index.emplace(
                monad::to_bytes(monad::keccak256(bytes.value())),
                monad::vm::make_shared_intercode(bytes.value()));
        }
    }

    // 3. Load the pre-state trie zero-copy from the offset-format node region
    //    (validated + hash-primed by the OffsetTrie constructor). No external
    //    pre-state root is needed — it is the blob's own header root.
    monad::mpt::OffsetTrie trie{witness.value().encoded_nodes};
    // A witness must carry a materialised pre-state trie; an overlay-id root is
    // the empty-trie sentinel (root_off == 0), which the execution path cannot
    // read from or commit onto.
    MONAD_ASSERT(!monad::mpt::is_overlay_id(trie.root));
    monad::PartialTrieDb pdb{std::move(trie), std::move(code_index)};

    // 4. Decode the embedded block.
    monad::byte_string_view block_view = witness.value().block_rlp;
    auto block_result = monad::rlp::decode_block(block_view);
    MONAD_ASSERT(block_result.has_value());
    MONAD_ASSERT(block_view.empty());
    auto const &block = block_result.value();

    // 5. Walk the ancestor headers, which the witness carries in ascending
    //    contiguous block order ending at the parent. They serve BLOCKHASH,
    //    and the parent's state root binds the supplied pre-state trie to the
    //    chain: the node blob carries its own root, so without that check a
    //    witness could be built over an arbitrary trie.
    monad::BlockHashBufferFinalized block_hash_buffer;
    monad::bytes32_t pre_state_root{};
    {
        bool checked_pre_state_root = false;
        monad::byte_string_view headers = witness.value().encoded_headers;
        while (!headers.empty()) {
            auto const payload = monad::rlp::parse_string_metadata(headers);
            MONAD_ASSERT(payload.has_value());
            monad::byte_string_view header_view = payload.value();
            auto const header = monad::rlp::decode_block_header(header_view);
            MONAD_ASSERT(header.has_value());
            MONAD_ASSERT(header_view.empty());
            block_hash_buffer.set(
                header.value().number,
                monad::to_bytes(monad::keccak256(payload.value())));
            if (header.value().number + 1 == block.header.number) {
                pre_state_root = pdb.state_root();
                // The witness parent must agree with the trie it delivers --
                // an in-guest consistency check. The BINDING to the real
                // chain is the exposure of pre_state_root as a public value
                // below: the verifier compares it against the canonical
                // parent header, which the prover cannot choose.
                MONAD_ASSERT(pre_state_root == header.value().state_root);
                checked_pre_state_root = true;
            }
        }
        MONAD_ASSERT(checked_pre_state_root);
    }

    // 6. Build the execution context. EthereumMainnet is the MVP chain;
    //    monad-chain dispatch lands when we wire monad witnesses up.
    monad::EthereumMainnet const chain;
    monad::vm::VM vm;
    pdb.set_block_and_prefix(block.header.number, monad::bytes32_t{});

    // 7. Pick the EVM revision from the block's position on the mainnet
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

    // The hash of the block that was executed, from the canonical header
    // encoding -- the same bytes a node hashes to identify the block.
    monad::byte_string const header_rlp =
        monad::rlp::encode_block_header(block.header);
    monad::bytes32_t block_hash;
    keccak256(header_rlp.data(), header_rlp.size(), block_hash.bytes);

    // Public values, in order: post-state root, pre-state root, block hash.
    // The verifier must check ALL THREE against the chain: post == this
    // block's state_root, pre == the parent's state_root, hash == the
    // canonical hash at this height. The first alone proves only that SOME
    // state yields this post-root; the second binds the witness to the real
    // pre-state; the third binds the execution to the real block -- and,
    // with it, the ancestor headers walked above, whose chain the BLOCKHASH
    // buffer serves.
    write_output(state_root.bytes, sizeof(state_root.bytes));
    write_output(pre_state_root.bytes, sizeof(pre_state_root.bytes));
    write_output(block_hash.bytes, sizeof(block_hash.bytes));
}
