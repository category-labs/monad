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

#include <cstring>
#include <zkvm/core/zkvm_io.h>
#include <zkvm/guest/execute_block_zkvm.hpp>

#include <span>

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

#ifdef MONAD_ZKVM_OFFICIAL_PROFILE
#if !defined(MONAD_ZKVM_ZISK_DMA_LOWERING) || !defined(MONAD_VM_TABLE_ARG) || \
    !defined(MONAD_ZKVM_KECCAKF_MEMO) || !MONAD_ZKVM_KECCAKF_MEMO ||          \
    !defined(MONAD_VM_FUSE_JUMPDEST) || !defined(MONAD_VM_FUSE_PUSH1OP) ||    \
    !defined(MONAD_VM_FUSE_PUSH2JUMP) || !defined(MONAD_VM_FUSE_TESTJUMPI)
#error "official ZisK profile is missing a required compile-time feature"
#endif
// Kept by zkvm/zisk/align.ld. The post-link audit requires this exact marker,
// so a manifest cannot be attached to an ELF built from a stale CMake cache.
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] =
    "monad-zkvm-official-v1;dma=1;table_arg=1;keccakf_memo=1;fuse=1;commit="
    MONAD_ZKVM_BUILD_COMMIT ";signature=" MONAD_ZKVM_BUILD_SIGNATURE;
#endif

#ifdef MONAD_ZKVM_KECCAK_SITES
#include <category/core/keccak_sites.hpp>
#else
#define MONAD_KECCAK_SITE(s, len) ((void)0)
#endif

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
        std::span<monad::byte_string_view const> const raw_transactions,
        monad::Db &pdb, monad::vm::VM &vm,
        monad::BlockHashBuffer const &block_hash_buffer)
    {
        return monad::execute_block_zkvm<traits>(
            chain,
            block,
            raw_transactions,
            pdb,
            vm,
            block_hash_buffer,
            monad::ChainContext<traits>{});
    }
}

#ifdef MONAD_ZKVM_SELFTEST
extern "C" std::uint32_t monad_zkvm_revert_semantics_test(void);
#endif

extern "C" void monad_zkvm_execute_witness(void)
{
#ifdef MONAD_ZKVM_SELFTEST
    // Self-test build: no witness is read. The first four output bytes are a bitmask -- bit N set
    // means case N failed, all zero means every case passed. Padded to 32 so the harness that
    // reads a root can read this too.
    {
        std::uint32_t const failures = monad_zkvm_revert_semantics_test();
        unsigned char out[32]{};
        __builtin_memcpy(out, &failures, sizeof(failures));
        write_output(out, sizeof(out));
        return;
    }
#endif
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
            // Hash the intercode's copy, not the witness bytes.
            //
            // Bytecode is the guest's longest keccak input -- 72 rate blocks a
            // call on 25815100 -- and it sits at whatever offset the witness
            // envelope left it at. 136 is a multiple of 8, so a misaligned
            // start makes every lane of every block a boundary-crossing load,
            // 159 against 17.
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
            MONAD_KECCAK_SITE(CODE_INDEX, bytes.value().size());
            code_index.emplace(
                monad::to_bytes(monad::keccak256(monad::byte_string_view{
                    code->code(), bytes.value().size()})),
                code);
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
    // The byte slice each transaction was decoded from, kept so the
    // transactions-root check can be made against those bytes rather than
    // against a re-encoding of what was decoded from them.
    std::vector<monad::byte_string_view> raw_transactions;
    auto block_result =
        monad::rlp::decode_block(block_view, &raw_transactions);
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
            // contiguous. Without this the buffer is keyed on the number a
            // header declares about itself, so every hash BLOCKHASH returns
            // for an ancestor would be the prover's to choose.
            if (have_prev) {
                MONAD_ASSERT(header.value().number == prev_number + 1);
                MONAD_ASSERT(header.value().parent_hash == prev_hash);
            }
            block_hash_buffer.set(header.value().number, hash);
            if (header.value().number + 1 == block.header.number) {
                // The newest ancestor is this block's parent, and block.header
                // is pinned by the published block hash. Anchoring the run
                // here is what ties the whole chain of them to the real chain;
                // the state-root check below binds only the trie.
                MONAD_ASSERT(hash == block.header.parent_hash);
                pre_state_root = pdb.state_root();
                // The witness parent must agree with the trie it delivers --
                // an in-guest consistency check. The BINDING to the real
                // chain is the exposure of pre_state_root as a public value
                // below: the verifier compares it against the canonical
                // parent header, which the prover cannot choose.
                MONAD_ASSERT(pre_state_root == header.value().state_root);
                checked_pre_state_root = true;
            }
            prev_hash = hash;
            prev_number = header.value().number;
            have_prev = true;
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
        SWITCH_EVM_TRAITS(
            dispatch, chain, block, raw_transactions, pdb, vm,
            block_hash_buffer);
        // SWITCH_EVM_TRAITS only covers Byzantium+; older revisions fall
        // through. execute_block_zkvm's static_assert requires
        // Spurious-Dragon+ anyway.
        return monad::BlockError::FieldBeforeFork;
    }();
    MONAD_ASSERT(root_result.has_value());

    monad::bytes32_t const &state_root = root_result.value();

    // The hash of the block that was executed, from the canonical header
    // encoding -- with the state root THIS RUN COMPUTED sealed into it, not the
    // one the witness supplied.
    //
    // That is what makes a single published value sufficient. The header commits
    // to every root it carries, so pinning its hash against the canonical chain
    // pins the state root through it: a computed root that differs by one bit
    // gives a different header, a different hash, and a rejected proof. The
    // parent is bound the same way -- parent_hash is a field of this header, and
    // the ancestor walk above asserts the supplied parent hashes to it and that
    // its state_root is the pre-state trie's own root.
    //
    // Encoding the witness's header instead would have left the verifier to
    // notice that the two disagree, which is a check nobody has written.
    auto sealed_header = block.header;
    sealed_header.state_root = state_root;
    monad::byte_string const header_rlp =
        monad::rlp::encode_block_header(sealed_header);
    monad::bytes32_t block_hash;
    MONAD_KECCAK_SITE(HEADER_HASH, header_rlp.size());
    keccak256(header_rlp.data(), header_rlp.size(), block_hash.bytes);

    // Public values, in order: post-state root, pre-state root, block hash.
    //
    // The THIRD ALONE is sufficient now that the computed root is sealed into
    // the header it hashes: checking it against the canonical hash at this
    // height binds the state root, the parent, and every other field the header
    // carries, in one comparison that cannot be half-applied. The first two are
    // published because they are useful to a caller and to the corpus gate, not
    // because the verifier needs them.
    //
    // Before the sealing above, all three had to be checked, and the check that
    // mattered most -- that the published post-root is the one the header
    // claims -- lived only in this comment. Kept here for the record: the first
    // alone proves only that SOME state yields this post-root; the second binds
    // the witness to the real pre-state; the third binds the execution to the
    // real block -- and,
    // with it, the ancestor headers walked above: the newest of them is
    // asserted to hash to block.header.parent_hash and each older one to be
    // named by its successor, so pinning this header pins the whole run the
    // BLOCKHASH buffer serves.
    write_output(state_root.bytes, sizeof(state_root.bytes));
    write_output(pre_state_root.bytes, sizeof(pre_state_root.bytes));
    write_output(block_hash.bytes, sizeof(block_hash.bytes));
#ifdef MONAD_ZKVM_KECCAK_SITES
    // Diagnostic tail, AFTER the three public values so their offsets are unchanged and the
    // verifier reads them exactly as before. A run that reports its keccak breakdown is therefore
    // still a run whose roots are checked -- which is the whole point of putting the counters here
    // rather than in a printf the guest cannot do.
    write_output(monad::keccak_sites::bytes(), monad::keccak_sites::size());
#endif
}
