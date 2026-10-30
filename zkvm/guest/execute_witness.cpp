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
#include <category/core/bit_primitives.hpp>
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
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/vm.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <utility>
#include <vector>

#if defined(MONAD_ZKVM_ZISK)
    #include <category/crypto/keccak.h>
    #include <zkvm/core/zkvm_halt.h>
#endif

#ifdef MONAD_ZKVM_SELFTEST
extern "C" std::uint32_t monad_zkvm_revert_semantics_test(void);
#endif

#ifdef MONAD_ZKVM_GAS_SELFTEST
extern "C" std::uint32_t monad_zkvm_deferred_gas_test();
extern "C" std::uint32_t monad_zkvm_deferred_gas_state_test();
#endif

extern "C" void monad_zkvm_execute_witness(void)
{
#ifdef MONAD_ZKVM_GAS_SELFTEST
    {
        std::uint32_t const failures = monad_zkvm_deferred_gas_test();
        unsigned char out[32]{};
        __builtin_memcpy(out, &failures, sizeof(failures));
        // Distinguish a completed test run from an empty or witness output.
        out[4] = 'G';
        out[5] = 'A';
        out[6] = 'S';
        out[7] = '2';
        std::uint32_t const state_failures =
            monad_zkvm_deferred_gas_state_test();
        __builtin_memcpy(out + 8, &state_failures, sizeof(state_failures));
        write_output(out, sizeof(out));
        return;
    }
#endif
#ifdef MONAD_ZKVM_SELFTEST
    // Self-test build: no witness is read. The first four output bytes are a
    // bitmask -- bit N set means case N failed, all zero means every case
    // passed. Padded to 32 so the harness that reads a root can read this too.
    {
        std::uint32_t const failures = monad_zkvm_revert_semantics_test();
        unsigned char out[32]{};
        __builtin_memcpy(out, &failures, sizeof(failures));
        write_output(out, sizeof(out));
        return;
    }
#endif
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

    // Seed maps before insertion with the canonical block hash. Reuse it as
    // output only after checking the computed state root against this header.
    monad_hash256 const block_hash =
        monad::keccak256(monad::rlp::encode_block_header(block.header));
    monad::bits::set_map_keys(block_hash.bytes);

    monad::vm::VM vm;
#ifndef MONAD_ZKVM_VARCODE_CACHE
    monad::CodeIndex code_index;
    // Reserve initial capacity to avoid rehashes while indexing bytecodes.
    code_index.reserve(512);
#endif
    {
        monad::byte_string_view codes = witness.value().encoded_codes;
        while (!codes.empty()) {
            auto const bytes = monad::rlp::parse_string_metadata(codes);
            MONAD_ASSERT(bytes.has_value());
            // Hash the intercode's existing aligned copy: witness slices may
            // be misaligned. Keccak's 136-byte blocks keep word loads aligned,
            // and no additional copy is needed.
            auto code = monad::vm::make_shared_intercode(bytes.value());
            // Check alignment and, in debug builds, unchanged bytecode.
            // The hash excludes the surrounding padding.
            MONAD_ASSERT((reinterpret_cast<uintptr_t>(code->code()) & 7) == 0);
            MONAD_DEBUG_ASSERT(
                std::memcmp(
                    code->code(), bytes.value().data(), bytes.value().size()) ==
                0);
#if defined(MONAD_ZKVM_ZISK)
            // Avoid memo lookup and insertion costs when hashing bytecode.
            // Repeated states are safe to recompute.
            monad::bytes32_t code_hash;
            monad_zkvm_keccak256_fast_nomemo(
                code->code(), bytes.value().size(), code_hash.bytes);
    #ifdef MONAD_ZKVM_VARCODE_CACHE
            vm.insert_varcode(code_hash, std::move(code));
    #else
            code_index.emplace(code_hash, code);
    #endif
#else
            code_index.emplace(
                monad::to_bytes(
                    monad::keccak256({code->code(), bytes.value().size()})),
                code);
#endif
        }
    }

    monad::mpt::OffsetTrie trie{witness.value().encoded_nodes};
    // A witness must carry a materialised pre-state trie; an overlay-id root
    // signifies an empty trie.
    MONAD_ASSERT(!monad::mpt::is_overlay_id(trie.root));
#ifdef MONAD_ZKVM_VARCODE_CACHE
    monad::PartialTrieDb pdb{std::move(trie), monad::CodeIndex{}};
#else
    monad::PartialTrieDb pdb{std::move(trie), std::move(code_index)};
#endif

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
                pre_state_root = pdb.state_root();
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
    pdb.set_block_and_prefix(block.header.number, monad::bytes32_t{});

    monad_eth_revision const rev =
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
            pdb,
            vm,
            block_hash_buffer);
        MONAD_ABORT("unsupported revision");
    }();
    MONAD_ASSERT(root_result.has_value());

    // Bind execution to the header hashed above before publishing its hash.
    MONAD_ASSERT(root_result.value() == block.header.state_root);
    write_output(block_hash.bytes, sizeof(block_hash.bytes));
#ifdef MONAD_ZKVM_ZISK
    // Output is flushed; skip destructors backed by the no-op guest free.
    zkvm_halt(0);
#endif
}
