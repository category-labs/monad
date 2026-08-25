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
#include <category/crypto/keccak.h>
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
#include <span>
#include <utility>
#include <vector>
#ifdef MONAD_ZKVM_KECCAK_SITES
#include <category/core/keccak_sites.hpp>
#else
#define MONAD_KECCAK_SITE(s, len) ((void)0)
#endif

#ifdef MONAD_ZKVM_OFFICIAL_PROFILE
// Kept by zkvm/zisk/align.ld. The audit requires the exact commit, build
// signature, runtime and feature set to occur in the linked ELF, so neither a
// stale CMake cache nor a differently configured binary can inherit an
// official manifest.
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] =
    "monad-zkvm-official-v2;runtime=ziskos-" MONAD_ZKVM_RUNTIME_VERSION
    ";features=" MONAD_ZKVM_BUILD_FEATURES ";commit=" MONAD_ZKVM_BUILD_COMMIT
    ";signature=" MONAD_ZKVM_BUILD_SIGNATURE;
#elif defined(MONAD_ZKVM_DEV_PROFILE)
// The same section, so the question "what is this binary" has an answer in
// every guest rather than only in the audited ones. An absent marker would
// have to be read as "not official", and absence is also what a stripped
// section, a truncated read or a older build looks like.
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] = "monad-zkvm-dev-v2";
#endif

extern "C" void monad_zkvm_execute_witness(void)
{
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());

    monad::CodeIndex code_index;
    {
        monad::byte_string_view codes = witness.value().encoded_codes;
        while (!codes.empty()) {
            auto const bytes = monad::rlp::parse_string_metadata(codes);
            MONAD_ASSERT(bytes.has_value());
            MONAD_KECCAK_SITE(CODE_INDEX, bytes.value().size());
            // Hash the intercode's copy, not the witness bytes.
            //
            // Bytecode is the guest's longest keccak input -- 72 rate blocks a
            // call on 25815100 -- and it sits at whatever offset the witness
            // envelope left it at. 136 is a multiple of 8, so a misaligned
            // start makes every lane of every block a boundary-crossing load,
            // 159 against 16.
            //
            // Intercode already owns an 8-aligned verbatim copy: `pad` takes it
            // from `new uint8_t[]` and returns it offset by a 32-byte prologue,
            // so `code()` keeps the alignment operator new gives. Building it
            // first and hashing from there costs no memory and no copy -- the
            // copy exists either way.
            auto const code = monad::vm::make_shared_intercode(bytes.value());
            // The two properties this depends on, checked rather than trusted:
            // the copy is 8-aligned, and it is the witness bytes unchanged.
            // Intercode pads around the code, never inside it, so the first
            // `size()` bytes at code() are verbatim -- but the padding is what
            // makes the alignment hold, so an assert here is what would catch a
            // change to it.
            MONAD_ASSERT(
                (reinterpret_cast<uintptr_t>(code->code()) & 7) == 0);
            MONAD_DEBUG_ASSERT(
                std::memcmp(
                    code->code(), bytes.value().data(),
                    bytes.value().size()) == 0);
            // Without the Keccak-f memo. Bytecode is 28,451 of the block's
            // 120,701 permutations and the 395 bodies are all distinct, so not
            // one state in a body's chain recurs: the memo files 2 x 1,232
            // cells per permutation and collects nothing. See
            // monad_zkvm_keccak256_fast_nomemo for the soundness argument.
            monad::bytes32_t code_hash;
            monad_zkvm_keccak256_fast_nomemo(
                code->code(), bytes.value().size(), code_hash.bytes);
            code_index.emplace(code_hash, code);
        }
    }

    monad::mpt::OffsetTrie trie{witness.value().encoded_nodes};
    // A witness must carry a materialised pre-state trie; an overlay-id root
    // signifies an empty trie.
    MONAD_ASSERT(!monad::mpt::is_overlay_id(trie.root));
    monad::PartialTrieDb pdb{std::move(trie), std::move(code_index)};

    monad::byte_string_view block_view = witness.value().block_rlp;
    // Keep each transaction's original bytes to verify transactions_root
    // without re-encoding the decoded transaction.
    std::vector<monad::byte_string_view> raw_transactions;
    auto block_result = monad::rlp::decode_block(block_view, raw_transactions);
    MONAD_ASSERT(block_result.has_value());
    MONAD_ASSERT(block_view.empty());
    auto const &block = block_result.value();

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
            MONAD_KECCAK_SITE(HEADER_HASH, payload.value().size());
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
    monad::vm::VM vm;
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

    monad::bytes32_t const &state_root = root_result.value();

    auto sealed_header = block.header;
    // commit to the computed state root
    sealed_header.state_root = state_root;
    monad::byte_string const header_rlp =
        monad::rlp::encode_block_header(sealed_header);
    MONAD_KECCAK_SITE(HEADER_HASH, header_rlp.size());
    monad_hash256 const block_hash = monad::keccak256(header_rlp);

    // Public value: the block hash alone is sufficient as the computed root is
    // sealed into the header it hashes
    write_output(block_hash.bytes, sizeof(block_hash.bytes));
#ifdef MONAD_ZKVM_KECCAK_SITES
    // Append diagnostic counters after the unchanged 32-byte block hash.
    write_output(monad::keccak_sites::bytes(), monad::keccak_sites::size());
#endif
}
