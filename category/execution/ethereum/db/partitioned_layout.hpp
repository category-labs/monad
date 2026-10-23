// Copyright (C) 2026 Category Labs, Inc.
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

#pragma once

// EIP-8297 "Partitioned Binary Tree" key embedding, laid over the mpt.
//
// The EIP merges the account and storage tries into one key space. Every key
// starts with a zone byte, then a hash-derived tree position, then a one byte
// sub-index. Keys of one zone have one fixed length, so the key set is prefix
// free:
//
//   account header   0x00 || H(addr32) || sub                   (34 bytes)
//   code chunk       0x01 || H(code_hash || idx32) || sub       (34 bytes)
//   storage          0xFF || H(addr32) || H(addr32 || idx32) || sub (66 bytes)
//
// H is state_key_hash (util.hpp): BLAKE3 in a blake3 build, keccak256
// otherwise, matching the node hash. addr32 is the 20 byte address left
// padded with zeros, idx32 is
// a 32 byte big-endian group index. Storage slots 0..63 live in the account
// header at sub-index 64 + slot; higher slots are grouped 256 per stem.
//
// This header gives the key derivations both as the spec's byte strings (for
// tests and tooling) and as mpt::Nibbles built from the key's components, which
// is what the trie is keyed with. Building from components keeps the stem a
// symbol-aligned prefix of every key under it at any MONAD_MPT_NIBBLE_BITS; the
// nibble key of a byte string key only equals the component form when a byte
// is a whole number of symbols.
//
// Deviations from the EIP, all for the mpt benchmark. The EIP only fixes the
// commitment; what a leaf stores is ours:
//   - the whole header stem is one leaf, at the stem key 0x00 || H(addr32)
//     itself: basic data, code hash, the monad Incarnation and the header
//     storage slots as a sparse page (encode_account_leaf). The EIP stores
//     basic data, the code hash and each header slot as its own 32 byte leaf
//     under the stem and has no incarnation; that split is a commitment
//     detail here: an EIP faithful commitment hashes this leaf as those
//     leaves, the mpt commitment hashes the leaf as is. One read brings the
//     account and its header slots, one write stores them, and the stem is
//     the leaf's path rather than a node;
//   - the header holds 128 slots (one storage_page_t), the EIP 64, so group 0
//     of the storage zone holds slots 128..255;
//   - code_size in basic data is 0 while code stays in the mpt's code table.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace partitioned
{
    // Tree embedding parameters (EIP-8297 "Tree embedding")
    inline constexpr uint8_t BASIC_DATA_LEAF_KEY = 0;
    inline constexpr uint8_t CODE_HASH_LEAF_KEY = 1;
    inline constexpr uint8_t DELEGATION_LEAF_KEY = 2;
    // Lookup key of the header slot page in the DbCache, the proposal post
    // state and Db::read_storage_page. Slot 0 is a header slot, so no storage
    // zone slot has this key.
    inline constexpr bytes32_t HEADER_PAGE_KEY{};
    inline constexpr unsigned HEADER_STORAGE_OFFSET = 64;
    inline constexpr unsigned HEADER_STORAGE_SLOTS = storage_page_t::SLOTS;
    inline constexpr unsigned STEM_SUBTREE_WIDTH = 256;
    inline constexpr unsigned char ACCOUNT_ZONE = 0x00;
    inline constexpr unsigned char CODE_ZONE = 0x01;
    inline constexpr unsigned char STORAGE_ZONE = 0xFF;
    inline constexpr size_t STEM_LENGTH = 1 + 32;
    inline constexpr size_t ACCOUNT_KEY_LENGTH = STEM_LENGTH + 1;
    inline constexpr size_t CODE_KEY_LENGTH = STEM_LENGTH + 1;
    inline constexpr size_t STORAGE_STEM_LENGTH = STEM_LENGTH + 32;
    inline constexpr size_t STORAGE_KEY_LENGTH = STORAGE_STEM_LENGTH + 1;
    inline constexpr size_t CODE_CHUNK_CODE_BYTES = 31;

    static_assert(
        HEADER_STORAGE_OFFSET + HEADER_STORAGE_SLOTS <= STEM_SUBTREE_WIDTH);

    // Basic data leaf layout (EIP-8297 "Header values")
    inline constexpr size_t BASIC_DATA_VERSION_OFFSET = 0;
    inline constexpr size_t BASIC_DATA_CODE_SIZE_OFFSET = 4;
    inline constexpr size_t BASIC_DATA_NONCE_OFFSET = 8;
    inline constexpr size_t BASIC_DATA_BALANCE_OFFSET = 16;
    inline constexpr size_t BASIC_DATA_BALANCE_BYTES = 16;

    // Symbol counts of the component-built trie keys (see the file comment)
    inline constexpr unsigned ZONE_NIBBLES = mpt::nibbles_for_bytes(1);
    inline constexpr unsigned SUB_INDEX_NIBBLES = mpt::nibbles_for_bytes(1);
    inline constexpr unsigned HASH_NIBBLES = mpt::nibbles_for_bytes(32);
    inline constexpr unsigned STEM_NIBBLES = ZONE_NIBBLES + HASH_NIBBLES;
    inline constexpr unsigned ACCOUNT_KEY_NIBBLES =
        STEM_NIBBLES + SUB_INDEX_NIBBLES;
    inline constexpr unsigned STORAGE_KEY_NIBBLES =
        STEM_NIBBLES + HASH_NIBBLES + SUB_INDEX_NIBBLES;

    using Stem = std::array<unsigned char, STEM_LENGTH>;
    using AccountKey = std::array<unsigned char, ACCOUNT_KEY_LENGTH>;
    using CodeKey = std::array<unsigned char, CODE_KEY_LENGTH>;
    using StorageKey = std::array<unsigned char, STORAGE_KEY_LENGTH>;

    //////////////////////////////////////////////////////////
    // Hashing and positions
    //////////////////////////////////////////////////////////

    bytes32_t key_hash(byte_string_view);
    bytes32_t address32(Address const &);
    // H(addr32)
    bytes32_t address_position(Address const &);
    // H(addr32 || idx32): the second digest of a storage stem
    bytes32_t storage_group_position(Address const &, bytes32_t const &group);
    // H(code_hash || idx32)
    bytes32_t code_group_position(bytes32_t const &code_hash, uint64_t group);

    //////////////////////////////////////////////////////////
    // Spec byte-string keys
    //////////////////////////////////////////////////////////

    Stem header_stem(Address const &);
    AccountKey header_key(Address const &, uint8_t sub_index);
    Stem storage_stem(Address const &);
    CodeKey code_chunk_key(bytes32_t const &code_hash, uint64_t chunk_id);

    // Where a storage slot lives: the header stem of its account, or a group
    // in the storage zone.
    struct StorageLocation
    {
        bool in_header;
        // H(addr32 || group) when !in_header
        bytes32_t group_position;
        uint8_t sub_index;
    };

    StorageLocation locate_storage(Address const &, bytes32_t const &slot);
    // Whether a slot lives in the header, and its offset there
    bool is_header_slot(bytes32_t const &slot);
    uint8_t header_slot_offset(bytes32_t const &slot);
    // The 34 or 66 byte key of a slot, as locate_storage places it.
    byte_string storage_key(Address const &, bytes32_t const &slot);

    //////////////////////////////////////////////////////////
    // Trie keys, as symbol strings built from the key components
    //////////////////////////////////////////////////////////

    mpt::Nibbles zone_nibbles(unsigned char zone);
    mpt::Nibbles sub_index_nibbles(uint8_t sub_index);
    mpt::Nibbles hash_nibbles(bytes32_t const &);
    // zone || H(addr32)
    mpt::Nibbles header_stem_nibbles(Address const &);
    mpt::Nibbles storage_stem_nibbles(Address const &);
    // Full keys relative to the state table
    mpt::Nibbles header_key_nibbles(Address const &, uint8_t sub_index);
    mpt::Nibbles storage_key_nibbles(Address const &, bytes32_t const &slot);
    mpt::Nibbles
    code_chunk_key_nibbles(bytes32_t const &code_hash, uint64_t chunk_id);

    //////////////////////////////////////////////////////////
    // Leaf values
    //////////////////////////////////////////////////////////

    // version, code_size, nonce, balance packed big-endian; the balance must
    // fit 16 bytes
    bytes32_t encode_basic_data(Account const &, uint32_t code_size = 0);

    // basic data to balance and nonce; the other fields come from their own
    // leaves. Returns nullopt for a malformed leaf.
    struct BasicData
    {
        uint8_t version;
        uint32_t code_size;
        uint64_t nonce;
        uint256_t balance;
    };

    std::optional<BasicData> decode_basic_data(byte_string_view);

    // The stored header leaf: basic data || code_hash || incarnation (8
    // bytes big-endian) || header slot page (encode_storage_page of the
    // header slots at their offsets). The first two 32 byte pieces are the
    // EIP's basic data and code hash leaves, the page its header slot leaves.
    inline constexpr size_t ACCOUNT_FIELDS_LENGTH = 32 + 32 + 8;
    byte_string encode_account_leaf(
        Account const &, storage_page_t const &header = {},
        uint32_t code_size = 0);

    struct AccountLeaf
    {
        Account account;
        storage_page_t header;
    };

    // Returns nullopt for a malformed leaf
    std::optional<AccountLeaf> decode_account_leaf(byte_string_view);

    // EIP-8297 chunkify_code: 31 code bytes per chunk behind a byte that
    // counts how many of them continue a PUSH from an earlier chunk. A chunk
    // that is 32 zero bytes is absent from the tree, like any zero value.
    std::vector<bytes32_t> chunkify_code(byte_string_view code);
    // Inverse: reassemble code_size bytes from chunks; a missing chunk reads
    // as zeros.
    byte_string unchunkify_code(
        std::vector<std::optional<bytes32_t>> const &chunks, size_t code_size);
}

MONAD_NAMESPACE_END
