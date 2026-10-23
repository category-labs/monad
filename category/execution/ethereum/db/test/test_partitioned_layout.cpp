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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/partitioned_layout.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <cstring>

using namespace monad;
using namespace monad::partitioned;
using namespace monad::literals;

namespace
{
    constexpr Address A = 0x1234567890abcdef1234567890abcdef12345678_address;

    bytes32_t slot(uint64_t const n)
    {
        return store_be_as<bytes32_t>(uint256_t{n});
    }

    byte_string_view view(auto const &arr)
    {
        return {arr.data(), arr.size()};
    }
}

// EIP-8297 test vectors ("Test Cases"). H is not pinned by the EIP, so these
// check the key shape around the digests computed by key_hash.
TEST(PartitionedLayout, header_key_vectors)
{
    bytes32_t const hA = address_position(A);
    EXPECT_EQ(hA, key_hash(to_byte_string_view(address32(A).bytes)));

    // basic data: 0x00 || H(A) || 0x00
    auto const basic = header_key(A, BASIC_DATA_LEAF_KEY);
    ASSERT_EQ(basic.size(), ACCOUNT_KEY_LENGTH);
    EXPECT_EQ(basic[0], ACCOUNT_ZONE);
    EXPECT_EQ(std::memcmp(basic.data() + 1, hA.bytes, 32), 0);
    EXPECT_EQ(basic[33], 0x00);

    // delegation: 0x00 || H(A) || 0x02
    auto const delegation = header_key(A, DELEGATION_LEAF_KEY);
    EXPECT_EQ(delegation[33], 0x02);

    // storage slot 5 lives in the header at sub-index 69
    auto const loc5 = locate_storage(A, slot(5));
    EXPECT_TRUE(loc5.in_header);
    EXPECT_EQ(loc5.sub_index, 0x45);
    auto const key5 = storage_key(A, slot(5));
    ASSERT_EQ(key5.size(), ACCOUNT_KEY_LENGTH);
    EXPECT_EQ(key5[0], ACCOUNT_ZONE);
    EXPECT_EQ(key5[33], 0x45);

    // the header holds one page of slots; the next slot is in the zone
    EXPECT_TRUE(locate_storage(A, slot(HEADER_STORAGE_SLOTS - 1)).in_header);
    EXPECT_FALSE(locate_storage(A, slot(HEADER_STORAGE_SLOTS)).in_header);
    EXPECT_EQ(HEADER_STORAGE_SLOTS, 128u);
}

TEST(PartitionedLayout, storage_key_vector)
{
    // slot 1000: tree_index 3, sub_index 232, key 0xFF || H(A) || H(A||3) ||
    // 0xE8
    auto const loc = locate_storage(A, slot(1000));
    EXPECT_FALSE(loc.in_header);
    EXPECT_EQ(loc.sub_index, 0xE8);
    EXPECT_EQ(loc.group_position, storage_group_position(A, slot(3)));

    auto const key = storage_key(A, slot(1000));
    ASSERT_EQ(key.size(), STORAGE_KEY_LENGTH);
    EXPECT_EQ(key[0], STORAGE_ZONE);
    EXPECT_EQ(std::memcmp(key.data() + 1, address_position(A).bytes, 32), 0);
    EXPECT_EQ(std::memcmp(key.data() + 33, loc.group_position.bytes, 32), 0);
    EXPECT_EQ(key[65], 0xE8);

    // H(A || 3) is the digest of addr32 followed by 32 byte big-endian 3
    unsigned char buf[64]{};
    std::memcpy(buf, address32(A).bytes, 32);
    buf[63] = 3;
    EXPECT_EQ(loc.group_position, key_hash({buf, sizeof(buf)}));

    // slots in one aligned group of 256 share the stem and differ only in the
    // last byte; a high bit anywhere above the last byte picks another group
    EXPECT_EQ(
        locate_storage(A, slot(1000)).group_position,
        locate_storage(A, slot(768)).group_position);
    EXPECT_NE(
        locate_storage(A, slot(1000)).group_position,
        locate_storage(A, slot(1024)).group_position);
    bytes32_t hashed_slot =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbe00_bytes32;
    bytes32_t group{};
    std::memcpy(group.bytes + 1, hashed_slot.bytes, 31);
    EXPECT_EQ(
        locate_storage(A, hashed_slot).group_position,
        storage_group_position(A, group));
    EXPECT_EQ(locate_storage(A, hashed_slot).sub_index, 0x00);
}

TEST(PartitionedLayout, code_chunk_key_vectors)
{
    bytes32_t const C =
        0x1111111111111111111111111111111111111111111111111111111111111111_bytes32;
    // chunk 5: 0x01 || H(C || 0) || 0x05
    auto const k5 = code_chunk_key(C, 5);
    ASSERT_EQ(k5.size(), CODE_KEY_LENGTH);
    EXPECT_EQ(k5[0], CODE_ZONE);
    EXPECT_EQ(
        std::memcmp(k5.data() + 1, code_group_position(C, 0).bytes, 32), 0);
    EXPECT_EQ(k5[33], 0x05);
    // chunk 300: 0x01 || H(C || 1) || 0x2C
    auto const k300 = code_chunk_key(C, 300);
    EXPECT_EQ(
        std::memcmp(k300.data() + 1, code_group_position(C, 1).bytes, 32), 0);
    EXPECT_EQ(k300[33], 0x2C);

    unsigned char buf[64]{};
    std::memcpy(buf, C.bytes, 32);
    buf[63] = 1;
    EXPECT_EQ(code_group_position(C, 1), key_hash({buf, sizeof(buf)}));
}

// The trie is keyed by symbol strings built from the key components. When a
// byte is a whole number of symbols that equals the nibbles of the byte string
// key; in every build the stem is a prefix of each key under it.
TEST(PartitionedLayout, nibble_keys)
{
    auto const stem = header_stem_nibbles(A);
    auto const basic = header_key_nibbles(A, BASIC_DATA_LEAF_KEY);
    auto const slot5 = storage_key_nibbles(A, slot(5));
    auto const slot1000 = storage_key_nibbles(A, slot(1000));
    auto const sstem = storage_stem_nibbles(A);

    EXPECT_TRUE(mpt::NibblesView{basic}.starts_with(stem));
    EXPECT_TRUE(mpt::NibblesView{slot5}.starts_with(stem));
    EXPECT_TRUE(mpt::NibblesView{slot1000}.starts_with(sstem));
    EXPECT_EQ(
        mpt::NibblesView{basic}.substr(stem.nibble_size()),
        mpt::NibblesView{sub_index_nibbles(BASIC_DATA_LEAF_KEY)});
    EXPECT_EQ(
        mpt::NibblesView{slot1000}.substr(sstem.nibble_size()),
        mpt::NibblesView{mpt::concat(
            mpt::NibblesView{
                hash_nibbles(locate_storage(A, slot(1000)).group_position)},
            mpt::NibblesView{sub_index_nibbles(0xE8)})});

    if constexpr (8 % mpt::NIBBLE_BITS == 0) {
        EXPECT_EQ(
            basic,
            mpt::concat(
                mpt::NibblesView{view(header_key(A, BASIC_DATA_LEAF_KEY))}));
        EXPECT_EQ(
            slot1000,
            mpt::concat(mpt::NibblesView{storage_key(A, slot(1000))}));
        EXPECT_EQ(
            code_chunk_key_nibbles(NULL_HASH, 300),
            mpt::concat(
                mpt::NibblesView{view(code_chunk_key(NULL_HASH, 300))}));
    }
}

TEST(PartitionedLayout, basic_data_roundtrip)
{
    Account const account{
        .balance =
            uint256_t{0x0123456789abcdefULL} << 64 | 0xfedcba9876543210ULL,
        .code_hash = NULL_HASH,
        .nonce = 0x1122334455667788ULL,
        .incarnation = Incarnation{7, 9}};
    bytes32_t const v = encode_basic_data(account, 0xabcdef);
    EXPECT_EQ(v.bytes[0], 0);
    EXPECT_EQ(v.bytes[1], 0);
    EXPECT_EQ(v.bytes[2], 0);
    EXPECT_EQ(v.bytes[3], 0);
    EXPECT_EQ(v.bytes[4], 0x00);
    EXPECT_EQ(v.bytes[5], 0xab);
    EXPECT_EQ(v.bytes[7], 0xef);
    EXPECT_EQ(v.bytes[8], 0x11);
    EXPECT_EQ(v.bytes[15], 0x88);
    EXPECT_EQ(v.bytes[16], 0x01);
    EXPECT_EQ(v.bytes[31], 0x10);

    auto const d = decode_basic_data(to_byte_string_view(v.bytes));
    ASSERT_TRUE(d.has_value());
    EXPECT_EQ(d->version, 0);
    EXPECT_EQ(d->code_size, 0xabcdefu);
    EXPECT_EQ(d->nonce, account.nonce);
    EXPECT_EQ(d->balance, account.balance);
    EXPECT_FALSE(decode_basic_data(byte_string_view{}).has_value());

    // an empty account packs to zero, which the tree stores as absent
    EXPECT_EQ(encode_basic_data(Account{}), bytes32_t{});

    // the stored header leaf is basic data || code hash || incarnation ||
    // header slot page
    storage_page_t header;
    header.set(5, v);
    header.set(63, account.code_hash);
    byte_string const leaf = encode_account_leaf(account, header, 0xabcdef);
    ASSERT_GT(leaf.size(), ACCOUNT_FIELDS_LENGTH);
    EXPECT_EQ(
        byte_string_view{leaf}.substr(0, 32), to_byte_string_view(v.bytes));
    EXPECT_EQ(
        byte_string_view{leaf}.substr(32, 32),
        to_byte_string_view(account.code_hash.bytes));
    auto const da = decode_account_leaf(leaf);
    ASSERT_TRUE(da.has_value());
    EXPECT_EQ(da->account, account);
    EXPECT_EQ(da->account.incarnation.get_block(), 7u);
    EXPECT_EQ(da->account.incarnation.get_tx(), 9u);
    EXPECT_EQ(da->header, header);
    EXPECT_EQ(da->header[5], v);
    EXPECT_EQ(da->header[6], bytes32_t{});

    // no header slots: the leaf is just the account fields
    byte_string const bare = encode_account_leaf(account);
    EXPECT_EQ(bare.size(), ACCOUNT_FIELDS_LENGTH);
    EXPECT_TRUE(decode_account_leaf(bare)->header.is_empty());
    EXPECT_FALSE(
        decode_account_leaf(byte_string_view{bare}.substr(1)).has_value());

    EXPECT_TRUE(is_header_slot(slot(0)));
    EXPECT_TRUE(is_header_slot(slot(127)));
    EXPECT_FALSE(is_header_slot(slot(128)));
    EXPECT_EQ(header_slot_offset(slot(127)), 127);
}

TEST(PartitionedLayout, chunkify_code)
{
    // EIP example: "... PUSH4 99 98 | 97 96 PUSH1 128 MSTORE ..." where | is
    // a chunk boundary; the second chunk reports two leading PUSHDATA bytes.
    byte_string code(28, 0x5b); // JUMPDEST filler
    code += 0x63; // PUSH4
    code += 99;
    code += 98; // chunk 0 ends after 31 bytes
    code += 97;
    code += 96;
    code += 0x60; // PUSH1
    code += 128;
    code += 0x52; // MSTORE
    auto const chunks = chunkify_code(code);
    ASSERT_EQ(chunks.size(), 2u);
    EXPECT_EQ(chunks[0].bytes[0], 0);
    EXPECT_EQ(chunks[0].bytes[29], 0x63);
    EXPECT_EQ(chunks[0].bytes[30], 99);
    EXPECT_EQ(chunks[0].bytes[31], 98);
    EXPECT_EQ(chunks[1].bytes[0], 2);
    EXPECT_EQ(chunks[1].bytes[1], 97);
    EXPECT_EQ(chunks[1].bytes[2], 96);
    EXPECT_EQ(chunks[1].bytes[3], 0x60);
    EXPECT_EQ(chunks[1].bytes[4], 128);
    EXPECT_EQ(chunks[1].bytes[5], 0x52);
    EXPECT_EQ(chunks[1].bytes[6], 0); // zero padded

    // a PUSH32 straddling three chunks: counts clamp at 31
    byte_string big(30, 0x00);
    big += 0x7f; // PUSH32 as the last byte of chunk 0
    big += byte_string(32, 0xaa);
    auto const c2 = chunkify_code(big);
    ASSERT_EQ(c2.size(), 3u);
    EXPECT_EQ(c2[1].bytes[0], 31);
    EXPECT_EQ(c2[2].bytes[0], 1);

    std::vector<std::optional<bytes32_t>> opt(c2.begin(), c2.end());
    EXPECT_EQ(unchunkify_code(opt, big.size()), big);
    opt[1] = std::nullopt;
    byte_string expect = big;
    std::fill(expect.begin() + 31, expect.begin() + 62, 0);
    EXPECT_EQ(unchunkify_code(opt, big.size()), expect);

    EXPECT_TRUE(chunkify_code({}).empty());
}
