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
#ifdef MONAD_ZKVM_L2
    #include <category/execution/ethereum/core/contract/big_endian.hpp>
    #include <zkvm/guest/decode_block_l2.hpp>
    #include <zkvm/guest/l2_config.hpp>
    #include <zkvm/guest/monad_l2_chain.hpp>
#endif

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <utility>
#include <vector>
#ifdef MONAD_ZKVM_KECCAK_SITES
    #include <category/core/keccak_sites.hpp>
#else
    #define MONAD_KECCAK_SITE(s, len) ((void)0)
#endif

#ifdef MONAD_ZKVM_OFFICIAL_PROFILE
// Retained by align.ld so the post-link audit can match the ELF to its
// commit, runtime, features and build signature.
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] =
    "monad-zkvm-official-v2;runtime=ziskos-" MONAD_ZKVM_RUNTIME_VERSION
    ";features=" MONAD_ZKVM_BUILD_FEATURES ";commit=" MONAD_ZKVM_BUILD_COMMIT
    ";signature=" MONAD_ZKVM_BUILD_SIGNATURE;
#elif defined(MONAD_ZKVM_DEV_PROFILE)
// Identify development builds explicitly; a missing marker is ambiguous.
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] = "monad-zkvm-dev-v2";
#endif

#ifdef MONAD_ZKVM_SELFTEST
extern "C" std::uint32_t monad_zkvm_revert_semantics_test(void);
#endif

#if defined(MONAD_ZKVM_ZISK)
namespace
{
    // Codes that share their first rate blocks share every Keccak-f state of
    // their chains up to where they first differ -- clones of one template
    // differ only at their immutables -- and those states recur: 519 of the
    // 23,304 bytecode permutations on block 25815159, 1,413 of 35,173 on
    // 25815000. A code that shares a prefix with another hashes that prefix
    // through the memo and the rest past it; every other code keeps the path
    // without it.
    constexpr size_t CODE_RATE = 136;

    // Looking for clones costs every code a key and a slot, about 38 steps,
    // and a witness needs enough bytecode to hold any: on the rtp 200 the nine
    // witnesses under 800 KiB of code carry 64 recurring permutations between
    // them, and the smallest above carries 105.
    constexpr size_t CODE_CLONES_MIN_BYTES = 800 * 1024;

    // The first code seen under each key, and the most rate blocks a later
    // code of that key shares with it. The key is the last word of the first
    // block, in the selector table that sets clones apart from other
    // contracts: codes whose first blocks agree share it, and codes that only
    // share it find no block in common. Open addressing, in a table that
    // starts zero as untouched memory does on the guest; past half full it
    // stops filing, and a code it has no slot for keeps the path without the
    // memo.
    class FirstBlocks
    {
    public:
        struct Slot
        {
            monad::vm::Intercode const *first; // null marks an empty slot
            uint64_t key;
            size_t first_depth;
        };

    private:
        static constexpr size_t SLOTS = 4096;
        Slot slots_[SLOTS];
        size_t used_;

    public:
        // `code`'s key's slot, tagged in bit 0, if `code` is the first there;
        // else the whole rate blocks it shares with that first code, shifted
        // past the tag.
        uintptr_t add(monad::vm::Intercode const &code)
        {
            uint64_t w;
            std::memcpy(&w, code.code() + CODE_RATE - 8, 8);
            uint64_t const key = w * 0x9E3779B97F4A7C15ull;
            size_t i = key >> 52;
            while (slots_[i].first != nullptr && slots_[i].key != key) {
                i = (i + 1) % SLOTS;
            }
            Slot &s = slots_[i];
            if (s.first == nullptr) {
                if (used_ == SLOTS / 2) {
                    return 0;
                }
                ++used_;
                s.first = &code;
                s.key = key;
                return reinterpret_cast<uintptr_t>(&s) | 1;
            }
            size_t const size = s.first->size();
            size_t const n =
                (code.size() < size ? code.size() : size) / CODE_RATE;
            size_t k = 0;
            while (k < n && std::memcmp(
                                code.code() + CODE_RATE * k,
                                s.first->code() + CODE_RATE * k,
                                CODE_RATE) == 0) {
                ++k;
            }
            if (k > s.first_depth) {
                s.first_depth = k;
            }
            return k << 1;
        }

        // The memo depth `add` left a code, once every code has been added.
        static size_t depth(uintptr_t const tag)
        {
            return (tag & 1) != 0
                       ? reinterpret_cast<Slot const *>(tag & ~uintptr_t{1})
                             ->first_depth
                       : tag >> 1;
        }
    };
}
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
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

#ifdef MONAD_ZKVM_L2
    // Eight fields, the last two the transaction-decryption secret and the
    // blinder's. A six-field witness fails here with InputTooShort, and an
    // eight-field one given to a plaintext guest fails with InputTooLong --
    // which is why the envelope carries no version byte.
    auto const witness = monad::parse_execution_witness_l2(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());
    auto const &w = witness.value().base;
#else
    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());
    auto const &w = witness.value();
#endif

    monad::CodeIndex code_index;
    // Reserve initial capacity to avoid rehashes while indexing bytecodes.
    code_index.reserve(512);
    {
        monad::byte_string_view codes = w.encoded_codes;
        // Hash the intercode's copy, not the witness bytes.
        //
        // Bytecode is the guest's longest keccak input -- 72 rate blocks a
        // call on 25815100 -- and it sits at whatever offset the witness
        // envelope left it at. 136 is a multiple of 8, so a misaligned start
        // makes every lane of every block a boundary-crossing load, 159
        // against 16.
        //
        // Intercode already owns an 8-aligned verbatim copy: `pad` takes it
        // from `new uint8_t[]` and returns it offset by a 32-byte prologue,
        // so `code()` keeps the alignment operator new gives. Building it
        // first and hashing from there costs no memory and no copy -- the
        // copy exists either way.
        auto const intercode_of = [](monad::byte_string_view const bytes) {
            MONAD_KECCAK_SITE(CODE_INDEX, bytes.size());
            auto code = monad::vm::make_shared_intercode(bytes);
            // The two properties this depends on, checked rather than
            // trusted: the copy is 8-aligned, and it is the witness bytes
            // unchanged. Intercode pads around the code, never inside it, so
            // the first `size()` bytes at code() are verbatim -- but the
            // padding is what makes the alignment hold, so an assert here is
            // what would catch a change to it.
            MONAD_ASSERT((reinterpret_cast<uintptr_t>(code->code()) & 7) == 0);
            MONAD_DEBUG_ASSERT(
                std::memcmp(code->code(), bytes.data(), bytes.size()) == 0);
            return code;
        };
        // Without the Keccak-f memo but for the prefix a code shares with
        // another: a body's chain recurs only as far as that prefix, and the
        // memo files 2 x 1,232 cells a permutation. See
        // monad_zkvm_keccak256_fast_nomemo for the soundness argument.
#if defined(MONAD_ZKVM_ZISK)
        if (codes.size() >= CODE_CLONES_MIN_BYTES) {
            // Every intercode first, each tagged with its memo depth: its own
            // shared blocks, or its key's slot when it is the first code there,
            // whose depth the later codes of the key raise. The key and the
            // compares read the aligned copies.
            struct Pending
            {
                monad::vm::SharedIntercode code;
                uintptr_t tag;
            };

            static FirstBlocks first_blocks;
            std::vector<Pending> pending;
            pending.reserve(512);
            while (!codes.empty()) {
                auto const bytes = monad::rlp::parse_string_metadata(codes);
                MONAD_ASSERT(bytes.has_value());
                auto code = intercode_of(bytes.value());
                uintptr_t const tag =
                    code->size() >= CODE_RATE ? first_blocks.add(*code) : 0;
                pending.push_back({std::move(code), tag});
            }
            for (Pending &p : pending) {
                size_t const depth = FirstBlocks::depth(p.tag);
                monad::bytes32_t code_hash;
                if (depth != 0) {
                    monad_zkvm_keccak256_fast_memo_prefix(
                        p.code->code(), p.code->size(), depth, code_hash.bytes);
                }
                else {
                    monad_zkvm_keccak256_fast_nomemo(
                        p.code->code(), p.code->size(), code_hash.bytes);
                }
                code_index.emplace(code_hash, std::move(p.code));
            }
        }
#endif
        while (!codes.empty()) {
            auto const bytes = monad::rlp::parse_string_metadata(codes);
            MONAD_ASSERT(bytes.has_value());
            auto const code = intercode_of(bytes.value());
            monad::bytes32_t code_hash;
#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_SP1)
            monad_zkvm_keccak256_fast_nomemo(
                code->code(), bytes.value().size(), code_hash.bytes);
#else
            // The memo-free entry exists only where the memo does: it is
            // defined under the same condition in keccak_accel.cpp and
            // declared only in the guest's shadow of keccak.h. This file is
            // compiled for the host runner too, where there is no memo to
            // leave out, so the digest is the ordinary one.
            monad_keccak256(
                code->code(), bytes.value().size(), code_hash.bytes);
#endif
            code_index.emplace(code_hash, code);
        }
    }

    monad::mpt::OffsetTrie trie{w.encoded_nodes};
    // A witness must carry a materialised pre-state trie; an overlay-id root
    // signifies an empty trie.
    MONAD_ASSERT(!monad::mpt::is_overlay_id(trie.root));
    monad::PartialTrieDb pdb{std::move(trie), std::move(code_index)};

    monad::byte_string_view block_view = w.block_rlp;
    // What the transactions-root check is taken over: the committed bytes,
    // rather than a re-encoding of what was decoded from them. On an L2 block
    // these are the ciphertext leaves, every one of them, including any that
    // were rejected -- the header commits to the whole list.
    std::vector<monad::byte_string_view> root_transactions;
#ifdef MONAD_ZKVM_L2
    // What each accepted transaction was decoded from, which its signing
    // payload is built from: the plaintexts, kept for the block.
    monad::byte_string plaintexts;
    std::vector<monad::byte_string_view> l2_encodings;
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

    // The state blinder, bound the same way and for a reason that needs saying
    // because it is not soundness. An unbound blinder costs nothing: the
    // commitment chain forces a prover to reuse whatever it picked, keccak256
    // binds it, and every proof still verifies. What an unbound blinder costs
    // is the confidentiality it exists for -- a producer supplying zeros
    // publishes an unblinded block hash, the state becomes testable by anyone
    // who can guess it, and nothing anywhere says so. Hence a compiled
    // commitment rather than trust.
    //
    // Asserted against extra_data, not written into it: the header arrives in
    // the witness and is hashed as given (see the sealing comment below), so
    // the only way to make the block hash blinded is to require that the
    // header already carries the right blinder.
    monad::bytes32_t const salt = monad::l2_state_salt(
        std::span<unsigned char const, 32>{
            witness.value().salt_secret.data(), 32},
        l2_header.number);
    MONAD_ASSERT(
        monad::to_bytes(monad::keccak256(witness.value().salt_secret)) ==
        monad::L2_SALT_COMMITMENT);
    MONAD_ASSERT(
        l2_header.extra_data.size() == sizeof(salt.bytes) &&
        std::memcmp(
            l2_header.extra_data.data(), salt.bytes, sizeof(salt.bytes)) == 0);
    MONAD_ASSERT(secret.has_value());
    auto block_result = monad::decode_block_l2(
        block_view,
        cipher_ctx,
        *secret,
        root_transactions,
        plaintexts,
        l2_encodings);
#else
    auto block_result = monad::rlp::decode_block(block_view, root_transactions);
#endif
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

#ifdef MONAD_ZKVM_L2
    // A chain id of its own and a revision that is a constant, not a lookup:
    // an L2 that starts at one revision has no fork schedule to consult. So the
    // revision is a type here and not a value, and no block number reaches it.
    monad::MonadL2 const chain;
    using L2Traits = monad::EvmTraits<monad::L2_REVISION>;
#else
    monad::EthereumMainnet const chain;
#endif
    monad::vm::VM vm;
    pdb.set_block_and_prefix(block.header.number, monad::bytes32_t{});

#ifndef MONAD_ZKVM_L2
    monad_eth_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);
#endif
    // The parent is the one the loop above authenticated: its hash is this
    // block's parent_hash and its state root is the pre-state trie's.
    auto const valid = [&]() -> monad::Result<void> {
#ifdef MONAD_ZKVM_L2
        return monad::static_validate_block_with_parent<L2Traits>(
            chain, block, parent_header);
#else
        SWITCH_EVM_TRAITS(
            static_validate_block_with_parent, chain, block, parent_header);
        MONAD_ABORT("unsupported revision");
#endif
    }();
    MONAD_ASSERT(valid.has_value());

    // The bytes each executed transaction was decoded from. On a plaintext
    // block they are the committed ones; on an L2 block the committed ones are
    // ciphertexts, one per leaf, so they are the plaintexts instead.
#ifdef MONAD_ZKVM_L2
    std::vector<monad::byte_string_view> const &transaction_encodings =
        l2_encodings;
#else
    std::vector<monad::byte_string_view> const &transaction_encodings =
        root_transactions;
#endif
    auto const root_result = [&]() -> monad::Result<monad::ZkvmBlockOutput> {
#ifdef MONAD_ZKVM_L2
        return monad::execute_block_zkvm<L2Traits>(
            chain,
            block,
            root_transactions,
            transaction_encodings,
            pdb,
            vm,
            block_hash_buffer);
#else
        SWITCH_EVM_TRAITS(
            execute_block_zkvm,
            chain,
            block,
            root_transactions,
            transaction_encodings,
            pdb,
            vm,
            block_hash_buffer);
        MONAD_ABORT("unsupported revision");
#endif
    }();
    MONAD_ASSERT(root_result.has_value());

    monad::bytes32_t const &state_root = root_result.value().state_root;

    auto sealed_header = block.header;
    // commit to the computed state root
    sealed_header.state_root = state_root;
    monad::byte_string const header_rlp =
        monad::rlp::encode_block_header(sealed_header);
    MONAD_KECCAK_SITE(HEADER_HASH, header_rlp.size());
    monad_hash256 const block_hash = monad::keccak256(header_rlp);

#ifdef MONAD_ZKVM_L2
    // The L2 publishes NEITHER state root, and that is the point rather than
    // an omission.
    //
    // A root is a commitment, and a commitment to a guessable value confirms
    // guesses -- see l2_state_salt for why this chain's state is guessable
    // from public data. So what goes out is the hash chain instead: this
    // block's hash, and the parent hash it names. Both are blinded, because
    // both headers carry the per-block blinder in extra_data.
    //
    // Nothing is lost, because the continuity the roots would carry is
    // established IN HERE and not by the verifier comparing them:
    //
    //   - the pre-state root is asserted equal to the newest ancestor
    //     header's state_root, and that header to hash to
    //     block.header.parent_hash (the ancestor walk above);
    //   - the post-state root is sealed into the header just above, so the
    //     block hash commits to it.
    //
    // The L1 therefore needs one comparison to chain a block to its parent --
    // this block's parent hash against the previous block's hash -- and it
    // reads no root to do it. Which also means the L1 never sees a root: the
    // hub's newStateRoot argument carries this block hash, a strictly stronger
    // commitment since it covers the root and every other header field, and
    // anything that ever wants the root itself would need the header revealed.
    // Withdrawals do not; they go through the anchor.
    write_output(
        block.header.parent_hash.bytes, sizeof(block.header.parent_hash.bytes));
    write_output(block_hash.bytes, sizeof(block_hash.bytes));

    // The anchor is NOT blinded, and cannot be: the L1 verifies merkle proofs
    // against it to release withdrawals. It is guessable the same way a root
    // is -- whoever guesses the messages recomputes it -- and the honest
    // statement of what that costs is that a message not yet relayed can be
    // confirmed early. Inherent to a root the L1 must open, not something the
    // blinder could fix.
    monad::bytes32_t const &anchor = root_result.value().namespace_anchor;
    write_output(anchor.bytes, sizeof(anchor.bytes));

    // Big-endian, like every other multi-byte quantity the header and the ABI
    // use; the keccak-site tail below is little-endian but explicitly
    // diagnostic, so it is not a precedent. Eight bytes rather than a padded
    // ABI word because this buffer is a packed struct -- the verifier
    // left-pads in one line.
    monad::u64_be const number{block.header.number};
    write_output(number.bytes, sizeof(number.bytes));
#else
    // Public value: the block hash alone is sufficient as the computed root is
    // sealed into the header it hashes.
    write_output(block_hash.bytes, sizeof(block_hash.bytes));
#endif
#ifdef MONAD_ZKVM_KECCAK_SITES
    // Append diagnostic counters after the unchanged public values. ZisK
    // commits 64 words of public output and ziskos asserts past them, so the
    // tail must fit behind what this build publishes.
    #ifdef MONAD_ZKVM_L2
    constexpr std::size_t publics = sizeof(block.header.parent_hash.bytes) +
                                    sizeof(block_hash.bytes) +
                                    sizeof(anchor.bytes) + sizeof(number.bytes);
    #else
    constexpr std::size_t publics = sizeof(block_hash.bytes);
    #endif
    static_assert(publics + monad::keccak_sites::size() <= 64 * 4);
    write_output(monad::keccak_sites::bytes(), monad::keccak_sites::size());
#endif
}
