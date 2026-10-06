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
#include <category/execution/ethereum/core/chain_hash.hpp>
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
    #include <category/execution/ethereum/sequencing_anchor.hpp>
    #include <zkvm/guest/domain_body.hpp>
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
    // The secret is checked here and the blinder applied at the end, to the
    // state root rather than to the header's extra_data: what this chain
    // publishes is a commitment to the root, so that is what has to be blinded.
    // A blinder in the header would protect a block hash nobody publishes.
    #ifdef MONAD_L2_HASH_POSEIDON2
    MONAD_ASSERT(
        monad::l2_salt_commitment(std::span<unsigned char const, 32>{
            witness.value().salt_secret.data(), 32}) ==
        monad::L2_SALT_COMMITMENT);
    #else
    // keccak's commitment is l2_salt_commitment's too, spelled out so the
    // keccak chain's guest keeps the bytes it compiles to without the switch.
    MONAD_ASSERT(
        monad::to_bytes(monad::keccak256(witness.value().salt_secret)) ==
        monad::L2_SALT_COMMITMENT);
    #endif
    MONAD_ASSERT(secret.has_value());
    auto body_result = monad::decode_domain_body(
        block_view,
        cipher_ctx,
        *secret,
        monad::L2_CHAIN_ID,
        root_transactions,
        plaintexts,
        l2_encodings);
    MONAD_ASSERT(body_result.has_value());
    MONAD_ASSERT(block_view.empty());
    auto const &block = body_result.value().block;
    // The previous DOMAIN block, which is not number - 1: an L1 block that
    // sequenced nothing for this domain produced no domain block at all.
    uint64_t const parent_number = body_result.value().parent_number;
    MONAD_ASSERT(parent_number < block.header.number);
#else
    auto block_result = monad::rlp::decode_block(block_view, root_transactions);
    MONAD_ASSERT(block_result.has_value());
    MONAD_ASSERT(block_view.empty());
    auto const &block = block_result.value();
#endif

    monad::WitnessBlockHashBuffer block_hash_buffer;
    monad::bytes32_t pre_state_root{};
#ifdef MONAD_ZKVM_L2
    // Ancestor HASHES, not headers. All BLOCKHASH needs is the hash, and the
    // continuity the headers used to carry -- the pre-state root against the
    // parent's state_root, that header against this block's parent_hash -- is
    // the hub's now: it compares the pre-state commitment this run publishes
    // against the one it already holds. 32 bytes an ancestor instead of 544.
    //
    // The run is contiguous and its newest entry is for number - 1, because a
    // domain block executes against an L1 header and the L1 leaves no gaps even
    // where this domain's own numbering does.
    {
        std::vector<monad::bytes32_t> hashes;
        monad::byte_string_view run = w.encoded_headers;
        while (!run.empty()) {
            auto const h = monad::rlp::parse_string_metadata(run);
            MONAD_ASSERT(h.has_value());
            MONAD_ASSERT(h.value().size() == sizeof(monad::bytes32_t));
            monad::bytes32_t hash;
            std::memcpy(hash.bytes, h.value().data(), sizeof(hash.bytes));
            hashes.push_back(hash);
        }
        MONAD_ASSERT(hashes.size() <= block.header.number);
        uint64_t n = block.header.number - hashes.size();
        for (auto const &hash : hashes) {
            block_hash_buffer.set(n++, hash);
        }
        // Taken as given. Nothing in here ties it to a state anyone accepted;
        // that tie is the published pre-state commitment's.
        pre_state_root = pdb.state_root();
    }
#else
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
                monad::to_bytes(monad::header_hash(payload.value()));
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
#endif

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
#ifndef MONAD_ZKVM_L2
    // The parent is the one the loop above authenticated: its hash is this
    // block's parent_hash and its state root is the pre-state trie's.
    //
    // Nothing of the sort on the domain path: the header is the L1's, which the
    // L1 validated against its own parent, and there is no parent domain header
    // to compare it to -- the domain's previous block may be many L1 blocks
    // back, and carries no header at all.
    auto const valid = [&]() -> monad::Result<void> {
        SWITCH_EVM_TRAITS(
            static_validate_block_with_parent, chain, block, parent_header);
        MONAD_ABORT("unsupported revision");
    }();
    MONAD_ASSERT(valid.has_value());
#endif

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
            block_hash_buffer,
            body_result.value().senders);
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

#ifndef MONAD_ZKVM_L2
    // Sealing the computed root into the header is what makes the block hash
    // sufficient on its own. The L2 arm publishes no block hash -- it has no
    // header of its own to hash -- so it does not seal, and does not pay the
    // encode and the permutation.
    auto sealed_header = block.header;
    sealed_header.state_root = state_root;
    monad::byte_string const header_rlp =
        monad::rlp::encode_block_header(sealed_header);
    MONAD_KECCAK_SITE(HEADER_HASH, header_rlp.size());
    monad_hash256 const block_hash = monad::header_hash(header_rlp);
#endif

#ifdef MONAD_ZKVM_L2
    // What a validator would sign, and nothing else. The proof stands in for a
    // quorum of them, so what it makes public is the digest's arguments:
    // stateTransitionDigest(domainChainId, domainBlockNumber, newStateRoot,
    // domainAnchor), plus the two values that digest does not reach -- the
    // input set, and the keys this run was bound to.
    //
    // No block hash, and no parent hash. They were published to chain a block
    // to its parent, and this chain does not chain that way: the hub orders
    // transitions with its own stateNonce and a strictly increasing block
    // number, and a domain block has no header of its own to hash.
    monad::u64_be const chain_id{monad::L2_CHAIN_ID};
    write_output(chain_id.bytes, sizeof(chain_id.bytes));
    monad::u64_be const number{block.header.number};
    write_output(number.bytes, sizeof(number.bytes));

    // The transition's two ends, so the hub chains by comparing the first
    // against the commitment it already holds for this domain. Nothing in here
    // establishes that link -- the pre-state root is checked against an
    // ancestor header the prover also supplied, which is internal consistency
    // and not a tie to what the hub accepted.
    //
    // Blinded with the PARENT's number, so this value is byte for byte what
    // that block's own run published as its final state. The hub's check is
    // then one equality and needs no derivation of its own.
    monad::bytes32_t const pre_commitment = monad::l2_state_commitment(
        std::span<unsigned char const, 32>{
            witness.value().salt_secret.data(), 32},
        parent_number,
        pre_state_root);
    write_output(pre_commitment.bytes, sizeof(pre_commitment.bytes));

    // The state root under this block's blinder, never the root itself. A
    // commitment to a guessable value confirms guesses, and on this chain the
    // state is guessable: the participants are registered on the L1, deposits
    // are public L1 transfers, and the ciphertexts were sequenced in the clear.
    // The hub stores this and reads it back without ever opening it, so an
    // opaque commitment serves it exactly as a bare root would.
    monad::bytes32_t const commitment = monad::l2_state_commitment(
        std::span<unsigned char const, 32>{
            witness.value().salt_secret.data(), 32},
        block.header.number,
        state_root);
    write_output(commitment.bytes, sizeof(commitment.bytes));

    // The anchor is NOT blinded, and cannot be: the L1 verifies merkle proofs
    // against it to release withdrawals. It is guessable the same way a root
    // is -- whoever guesses the messages recomputes it -- and the honest
    // statement of what that costs is that a message not yet relayed can be
    // confirmed early. Inherent to a root the L1 must open, not something the
    // blinder could fix.
    monad::bytes32_t const &anchor = root_result.value().domain_anchor;
    write_output(anchor.bytes, sizeof(anchor.bytes));

    // The inputs this run was handed, so a verifier can tell WHICH ciphertexts
    // produced the commitment above. Nothing else published here does.
    //
    // Over root_transactions and not over the executed set, which is the whole
    // point -- it holds every leaf the list carried, including the ones the
    // cipher refused, so a prover cannot narrow the input set and then attest a
    // digest of its own choosing. See sequencing_anchor.hpp.
    monad::bytes32_t const sequencing = monad::sequencing_anchor(
        monad::L2_CHAIN_ID, block.header.number, root_transactions);
    write_output(sequencing.bytes, sizeof(sequencing.bytes));

    // The two keys this run was bound to, published rather than left implicit
    // in the ELF so that rotating either does not change the verification key.
    // The hub checks them against what it has registered for this domain;
    // without that check the rotation argument would cost the binding, and a
    // prover supplying any secret could decrypt to a different set of
    // transactions and prove a valid post-state for a block nobody wrote.
    unsigned char viewing_pk[33];
    viewing_pk[0] = monad::L2_OPERATOR_PK_ODD ? 0x03 : 0x02;
    std::memcpy(
        viewing_pk + 1,
        monad::L2_OPERATOR_PK_X.bytes,
        sizeof(monad::L2_OPERATOR_PK_X.bytes));
    write_output(viewing_pk, sizeof(viewing_pk));
    write_output(
        monad::L2_SALT_COMMITMENT.bytes,
        sizeof(monad::L2_SALT_COMMITMENT.bytes));
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
    constexpr std::size_t publics =
        sizeof(chain_id.bytes) + sizeof(number.bytes) +
        sizeof(pre_commitment.bytes) + sizeof(commitment.bytes) +
        sizeof(anchor.bytes) + sizeof(sequencing.bytes) + sizeof(viewing_pk) +
        sizeof(monad::L2_SALT_COMMITMENT.bytes);
    #else
    constexpr std::size_t publics = sizeof(block_hash.bytes);
    #endif
    static_assert(publics + monad::keccak_sites::size() <= 64 * 4);
    write_output(monad::keccak_sites::bytes(), monad::keccak_sites::size());
#endif
}
