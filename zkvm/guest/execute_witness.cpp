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

#include <io-interface/zkvm_io.h>
#include <zkvm/guest/execute_block.hpp>
#include <zkvm/guest/witness_block_hash_buffer.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/crypto/hash256.h>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/vm.hpp>
#include <zkvm/state/key_hash.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

extern "C" void monad_zkvm_execute_witness(void)
{
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());

    monad::byte_string_view block_view = witness.value().block_rlp;
    // Keep each transaction's original bytes to verify transactions_root
    // without re-encoding the decoded transaction.
    std::vector<monad::byte_string_view> raw_transactions;
    auto block_result = monad::rlp::decode_block(block_view, raw_transactions);
    MONAD_ASSERT(block_result.has_value());
    MONAD_ASSERT(block_view.empty());
    auto const &block = block_result.value();

    // The state's tables are keyed from this block's hash (see
    // zkvm/state/key_hash.hpp), so the seed comes before any of them.
    monad::zkvm::KeySeed const seed =
        monad::zkvm::KeySeed::from_block_hash(monad::to_bytes(
            monad::keccak256(monad::rlp::encode_block_header(block.header))));

    monad::vm::VM vm;
    monad::State::CodeTable codes{0, monad::zkvm::Bytes32Hash{seed}};
    {
        monad::byte_string_view encoded = witness.value().encoded_codes;
        while (!encoded.empty()) {
            auto const bytes = monad::rlp::parse_string_metadata(encoded);
            MONAD_ASSERT(bytes.has_value());
            auto const hash = monad::to_bytes(monad::keccak256(bytes.value()));
            codes.try_emplace(
                hash, vm.try_insert_varcode_raw(hash, bytes.value()));
        }
    }

    monad::mpt::OffsetTrie trie{witness.value().encoded_nodes};
    // A witness must carry a materialised pre-state trie; an overlay-id root
    // signifies an empty trie.
    MONAD_ASSERT(!monad::mpt::is_overlay_id(trie.root));
    monad::State state{
        std::move(trie), std::move(codes), vm, block.header.number, seed};

    monad::WitnessBlockHashBuffer block_hash_buffer;
    monad::bytes32_t pre_state_root{};
    monad::BlockHeader parent_header{};
    {
        bool checked_pre_state_root = false;
        bool have_prev = false;
        monad::bytes32_t prev_hash{};
        uint64_t prev_number = 0;
        monad::byte_string_view headers = witness.value().encoded_headers;
        while (!headers.empty()) {
            auto const payload = monad::rlp::parse_string_metadata(headers);
            MONAD_ASSERT(payload.has_value());
            monad::byte_string_view header_view = payload.value();
            auto const header = monad::rlp::decode_block_header(header_view);
            MONAD_ASSERT(header.has_value());
            MONAD_ASSERT(header_view.empty());
            monad::bytes32_t const hash =
                monad::to_bytes(monad::keccak256(payload.value()));
            // Each header must name the one before it, and the run must be
            // contiguous.
            if (have_prev) {
                MONAD_ASSERT(header.value().number == prev_number + 1);
                MONAD_ASSERT(header.value().parent_hash == prev_hash);
            }
            block_hash_buffer.set(header.value().number, hash);
            if (header.value().number + 1 == block.header.number) {
                // The last header is this block's parent
                MONAD_ASSERT(
                    hash == block.header.parent_hash && headers.empty());
                pre_state_root = state.state_root();
                MONAD_ASSERT(pre_state_root == header.value().state_root);
                parent_header = header.value();
                checked_pre_state_root = true;
            }
            prev_hash = hash;
            prev_number = header.value().number;
            have_prev = true;
        }
        MONAD_ASSERT(checked_pre_state_root);
    }

    monad::EthereumMainnet const chain;

    monad::EvmRevision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);
    // The parent is the one the loop above authenticated: its hash is this
    // block's parent_hash and its state root is the pre-state trie's.
    auto const valid = [&]() -> monad::Result<void> {
        SWITCH_EVM_TRAITS(
            static_validate_block_with_parent, chain, block, parent_header);
        MONAD_ABORT("unsupported revision");
    }();
    MONAD_ASSERT(valid.has_value());

    auto const root_result = [&]() -> monad::Result<monad::bytes32_t> {
        SWITCH_EVM_TRAITS(
            execute_block_zkvm,
            chain,
            block,
            raw_transactions,
            state,
            block_hash_buffer);
        MONAD_ABORT("unsupported revision");
    }();
    MONAD_ASSERT(root_result.has_value());

    monad::bytes32_t const &state_root = root_result.value();

    auto sealed_header = block.header;
    // commit to the computed state root
    sealed_header.state_root = state_root;
    monad::byte_string const header_rlp =
        monad::rlp::encode_block_header(sealed_header);
    monad_hash256 const block_hash = monad::keccak256(header_rlp);

    // Public value: the block hash alone is sufficient as the computed root is
    // sealed into the header it hashes
    write_output(block_hash.bytes, sizeof(block_hash.bytes));
}
