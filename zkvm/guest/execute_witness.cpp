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
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{input, input_len});
    MONAD_ASSERT(witness.has_value());

    monad::CodeIndex code_index;
    // Reserve initial capacity to avoid rehashes while indexing bytecodes.
    code_index.reserve(512);
    {
        monad::byte_string_view codes = witness.value().encoded_codes;
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
            // The memo-free entry exists only with the guest memo; the host
            // runner uses ordinary Keccak because it has no memo to bypass.
            monad_keccak256(
                code->code(), bytes.value().size(), code_hash.bytes);
#endif
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
