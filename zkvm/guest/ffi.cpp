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
// block sequentially via execute_block_zkvm<traits>, and commit the public
// output: three roots on the Ethereum arm, and under MONAD_ZKVM_L2 the message
// anchor and the block number after them. See the comment at the write_output
// calls for what each value is for and what it is worth.
//
// The Rust ZisK / SP1 guest crates link this library and call
// monad_zkvm_execute_witness from their respective entrypoints. The C++
// side owns input/output via the eth-act standard interface
// (zkvm/core/zkvm_io.h):
//   - read_input(...)  — fetches the RLP-encoded witness buffer
//   - write_output(...) — appends to the committed public output, one call a
//     value; ZisK's ROM publishes that region with its `pubout` operation, in
//     32 chunks of 64 bits, which is where the 256-byte cap comes from
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
#ifdef MONAD_ZKVM_L2
    #include <category/execution/ethereum/core/contract/big_endian.hpp>
    #include <zkvm/guest/decode_block_l2.hpp>
    #include <zkvm/guest/l2_config.hpp>
    #include <zkvm/guest/monad_l2_chain.hpp>
#endif
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
    #if !defined(MONAD_ZKVM_ZISK_DMA_LOWERING) ||                              \
        !defined(MONAD_VM_TABLE_ARG) || !defined(MONAD_ZKVM_KECCAKF_MEMO) ||   \
        !MONAD_ZKVM_KECCAKF_MEMO || !defined(MONAD_VM_FUSE_JUMPDEST) ||        \
        !defined(MONAD_VM_FUSE_PUSH1OP) ||                                     \
        !defined(MONAD_VM_FUSE_PUSH2JUMP) || !defined(MONAD_VM_FUSE_TESTJUMPI)
        #error                                                                 \
            "official ZisK profile is missing a required compile-time feature"
    #endif
// Kept by zkvm/zisk/align.ld. The post-link audit requires this exact marker,
// so a manifest cannot be attached to an ELF built from a stale CMake cache.
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] =
    "monad-zkvm-official-v1;dma=1;table_arg=1;keccakf_memo=1;fuse=1;"
    "commit=" MONAD_ZKVM_BUILD_COMMIT ";signature=" MONAD_ZKVM_BUILD_SIGNATURE;
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
    monad::Result<monad::ZkvmBlockOutput> dispatch(
        monad::Chain const &chain, monad::Block const &block,
        std::span<monad::byte_string_view const> const root_transactions,
        monad::Db &pdb, monad::vm::VM &vm,
        monad::BlockHashBuffer const &block_hash_buffer)
    {
        return monad::execute_block_zkvm<traits>(
            chain,
            block,
            root_transactions,
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
    // 1. Read + parse the witness.
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

#if defined(MONAD_ZKVM_L2) && !defined(MONAD_ZKVM_L2_PLAINTEXT_LEAVES)
    // Seven fields, the seventh being the transaction-decryption secret. A
    // six-field witness fails here with InputTooShort, and a seven-field one
    // given to a plaintext guest fails with InputTooLong -- which is why the
    // envelope carries no version byte.
    auto const witness = monad::parse_execution_witness_l2(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());
    auto const &w = witness.value().base;
#else
    // Six fields under MONAD_ZKVM_L2_PLAINTEXT_LEAVES too: that arm is the
    // differential's reference, so it reads the ORIGINAL witness -- no secret,
    // and leaves that are already transactions.
    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());
    auto const &w = witness.value();
#endif

    // 2. Build the code index from the witness bytecodes (keccak-keyed), the
    //    same content PartialTrieDb serves read_code from.
    monad::CodeIndex code_index;
    // Floored: about four hundred bytecodes a block, inserted one at a time
    // into a map that starts empty, and a rehash recomputes every key it holds.
    code_index.reserve(512);
    {
        monad::byte_string_view codes = w.encoded_codes;
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
            MONAD_ASSERT((reinterpret_cast<uintptr_t>(code->code()) & 7) == 0);
            MONAD_DEBUG_ASSERT(
                std::memcmp(
                    code->code(), bytes.value().data(), bytes.value().size()) ==
                0);
            MONAD_KECCAK_SITE(CODE_INDEX, bytes.value().size());
            // Without the Keccak-f memo. Bytecode is 28,451 of the block's
            // 120,701 permutations and the 395 bodies are all distinct, so not
            // one state in a body's chain recurs: the memo files 2 x 1,232
            // cells per permutation and collects nothing. See
            // monad_zkvm_keccak256_fast_nomemo for the soundness argument.
            monad::bytes32_t code_hash;
            keccak256_nomemo(
                code->code(), bytes.value().size(), code_hash.bytes);
            code_index.emplace(code_hash, code);
        }
    }

    // 3. Load the pre-state trie zero-copy from the offset-format node region
    //    (validated + hash-primed by the OffsetTrie constructor). No external
    //    pre-state root is needed — it is the blob's own header root.
    monad::mpt::OffsetTrie trie{w.encoded_nodes};
    // A witness must carry a materialised pre-state trie; an overlay-id root is
    // the empty-trie sentinel (root_off == 0), which the execution path cannot
    // read from or commit onto.
    MONAD_ASSERT(!monad::mpt::is_overlay_id(trie.root));
    monad::PartialTrieDb pdb{std::move(trie), std::move(code_index)};

    // 4. Decode the embedded block.
    monad::byte_string_view block_view = w.block_rlp;
    // What the transactions-root check is taken over: the committed bytes,
    // rather than a re-encoding of what was decoded from them. On an L2 block
    // these are the ciphertext leaves, every one of them, including any that
    // were rejected -- the header commits to the whole list.
    std::vector<monad::byte_string_view> root_transactions;
#if defined(MONAD_ZKVM_L2) && !defined(MONAD_ZKVM_L2_PLAINTEXT_LEAVES)
    // The cipher context is a function of the header and of compiled protocol
    // constants, so it has to be in hand before the first leaf is decrypted --
    // hence one extra pass over the header, which is a single RLP list. It
    // stays a PARAMETER of decode_block_l2 rather than being built inside it,
    // so a test can inject one without the deployment constants.
    monad::BlockHeader l2_header;
    {
        monad::byte_string_view view = block_view;
        auto payload = monad::rlp::parse_list_metadata(view);
        MONAD_ASSERT(payload.has_value());
        auto header = monad::rlp::decode_block_header(payload.value());
        MONAD_ASSERT(header.has_value());
        l2_header = std::move(header).value();
    }
    auto const cipher_ctx = monad::l2_cipher_context(l2_header);
    // The one check the whole design rests on, and it is in the type rather
    // than in a call: the secret is a private witness input, so without tying
    // it to the compiled operator key a prover supplies any secret, gets
    // another set of plaintexts, and proves a valid post-state for a block
    // nobody wrote. bind_secret is the only source of an L2Cipher::Secret, so
    // decode_block_l2 cannot be reached with an unbound one. A failure here is
    // a malformed witness, like every other witness defect in this function.
    auto const secret = monad::L2Cipher::bind_secret(
        cipher_ctx,
        std::span<unsigned char const, 32>{witness.value().sk.data(), 32});
    MONAD_ASSERT(secret.has_value());
    auto block_result = monad::decode_block_l2(
        block_view, cipher_ctx, *secret, root_transactions);
#else
    // Also the MONAD_ZKVM_L2_PLAINTEXT_LEAVES path. Everything else about that
    // build is the L2 -- the chain, the unpriced gas, the block shape, the
    // anchor -- so a run of it against an encrypted run of the same block
    // differs by the cipher and by nothing else. That is the whole argument
    // the corpus differential makes, and comparing against a NON-L2 build
    // cannot make it: gas is priced there, so the sender's balance, the refund
    // and the beneficiary's tips all move on one arm and not the other.
    auto block_result =
        monad::rlp::decode_block(block_view, &root_transactions);
#endif
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
        monad::byte_string_view headers = w.encoded_headers;
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
#ifdef MONAD_ZKVM_L2
    // A chain id of its own and a revision that is a constant, not a lookup:
    // an L2 that starts at one revision has no fork schedule to consult.
    monad::MonadL2 const chain;
#else
    monad::EthereumMainnet const chain;
#endif
    monad::vm::VM vm;
    pdb.set_block_and_prefix(block.header.number, monad::bytes32_t{});

    // 7. Pick the EVM revision from the block's position on the mainnet
    //    fork schedule and dispatch into the templated guest pipeline. The
    //    witness is assumed to carry a real Ethereum block, so its number
    //    and timestamp select the revision the same way the live node does.
    monad_eth_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);
    auto const root_result = [&]() -> monad::Result<monad::ZkvmBlockOutput> {
        SWITCH_EVM_TRAITS(
            dispatch,
            chain,
            block,
            root_transactions,
            pdb,
            vm,
            block_hash_buffer);
        // SWITCH_EVM_TRAITS only covers Byzantium+; older revisions fall
        // through. execute_block_zkvm's static_assert requires
        // Spurious-Dragon+ anyway.
        return monad::BlockError::FieldBeforeFork;
    }();
    MONAD_ASSERT(root_result.has_value());

    monad::bytes32_t const &state_root = root_result.value().state_root;

    // The hash of the block that was executed, from the canonical header
    // encoding -- with the state root THIS RUN COMPUTED sealed into it, not the
    // one the witness supplied.
    //
    // That is what makes a single published value sufficient. The header
    // commits to every root it carries, so pinning its hash against the
    // canonical chain pins the state root through it: a computed root that
    // differs by one bit gives a different header, a different hash, and a
    // rejected proof. The parent is bound the same way -- parent_hash is a
    // field of this header, and the ancestor walk above asserts the supplied
    // parent hashes to it and that its state_root is the pre-state trie's own
    // root.
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
#ifdef MONAD_ZKVM_L2
    // The tuple the L1 hub verifies: submitStateSignature(chainId,
    // blockNumber, newStateRoot, anchor). chainId is compiled into this guest,
    // so only these two join the three above.
    //
    // Neither weakens the argument above; both lean on it. The block number IS
    // a field of the sealed header, and the anchor is a deterministic function
    // of the block's logs, which receipts_root commits to and the header
    // carries. They are published so the verifier can rebuild the digest
    // without carrying the header, not because they add anything to trust.
    //
    // Big-endian, like every other multi-byte quantity the header and the ABI
    // use; the keccak-site tail below is little-endian but explicitly
    // diagnostic, so it is not a precedent. Eight bytes rather than a padded
    // ABI word because this buffer is a packed struct -- the verifier
    // left-pads in one line.
    monad::bytes32_t const &anchor = root_result.value().namespace_anchor;
    write_output(anchor.bytes, sizeof(anchor.bytes));
    monad::u64_be const number{block.header.number};
    write_output(number.bytes, sizeof(number.bytes));
#endif
#ifdef MONAD_ZKVM_KECCAK_SITES
    // Diagnostic tail, AFTER the verifier's values so their offsets are
    // unchanged and it reads them exactly as before. A run that reports its
    // keccak breakdown is therefore still a run whose roots are checked --
    // which is the whole point of putting the counters here rather than in a
    // printf the guest cannot do.
    //
    // This tail is 2 * 19 * 4 = 152 bytes and the three roots are 96, so a
    // diagnostic run commits 248 of ZisK's 256. MONAD_ZKVM_L2's two extra
    // values take the head to 136 and the total to 288, which is why the two
    // options are a configure-time error together rather than an overflow.
    write_output(monad::keccak_sites::bytes(), monad::keccak_sites::size());
#endif
}
