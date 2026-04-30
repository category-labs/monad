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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <functional>
#include <random>
#include <variant>

using namespace monad;

namespace
{
    constexpr auto PRE_ROOT =
        0x0101010101010101010101010101010101010101010101010101010101010101_bytes32;
    constexpr auto POST_ROOT =
        0x0202020202020202020202020202020202020202020202020202020202020202_bytes32;

    byte_string make_minimal_witness(
        bytes32_t const &pre, bytes32_t const &post,
        byte_string nodes_payload = {}, byte_string codes_payload = {})
    {
        return rlp::encode_list2(
            rlp::encode_string2({}), // [0] block_rlp (empty)
            rlp::encode_string2(
                byte_string_view{pre.bytes, 32}), // [1] pre_state_root
            rlp::encode_string2(
                byte_string_view{post.bytes, 32}), // [2] post_state_root
            rlp::encode_list2(nodes_payload), // [3] node preimages
            rlp::encode_list2(codes_payload), // [4] contract bytecodes
            byte_string{
                static_cast<unsigned char>(0xc0)}, // [5] preimages (skipped)
            byte_string{static_cast<unsigned char>(0xc0)}
            // [6] ancestor headers
        );
    }

    void storage_leaf_roundtrip(
        bytes32_t const &val, NodeIndex &nodes, std::string_view label = {})
    {
        byte_string const enc = StorageLeafValue::encode(StorageLeafValue{val});

        byte_string_view view{enc};
        auto const decoded = StorageLeafValue::decode(view, nodes);
        ASSERT_FALSE(decoded.has_error()) << label;
        EXPECT_EQ(decoded.value().value, val) << label;
        ASSERT_TRUE(view.empty()) << label;
    }

    byte_string
    make_branch_with_child(unsigned slot, byte_string const &child_rlp)
    {
        byte_string body;
        for (unsigned i = 0; i < 16; ++i) {
            body += (i == slot) ? child_rlp : rlp::EMPTY_STRING;
        }
        body += rlp::EMPTY_STRING; // value slot
        return rlp::encode_list2(body);
    }

    Result<PartialTrieDb<NoopAccessTracker>>
    db_from_rlp_node(byte_string const &node_rlp)
    {
        bytes32_t const root = to_bytes(
            keccak256(byte_string_view{node_rlp.data(), node_rlp.size()}));
        byte_string const encoded_nodes = rlp::encode_string2(
            byte_string_view{node_rlp.data(), node_rlp.size()});
        return PartialTrieDb<NoopAccessTracker>::from_reth_witness(
            root,
            byte_string_view{encoded_nodes.data(), encoded_nodes.size()},
            {});
    }

    PartialTrieDb<NoopAccessTracker> make_empty_db()
    {
        auto result = PartialTrieDb<NoopAccessTracker>::from_reth_witness(
            NULL_ROOT, {}, {});
        MONAD_ASSERT(!result.has_error());
        return std::move(result.value());
    }

    void commit_with(
        PartialTrieDb<NoopAccessTracker> &db, BlockHeader const &header,
        StateDeltas const &deltas,
        std::function<void(BlockHeader &)> populate = [](BlockHeader &) {})
    {
        CommitBuilder builder(header.number);
        db.commit(bytes32_t{}, builder, header, deltas, std::move(populate));
    }

    /// Build a witness whose only node is a leaf for `addr` with the given
    /// account and an empty storage trie.
    Result<PartialTrieDb<NoopAccessTracker>>
    db_from_account(Address const &addr, Account const &acct)
    {
        auto const path_bytes = keccak256(addr.bytes);
        mpt::Nibbles leaf_path{mpt::NibblesView{path_bytes}};

        unsigned char compact_buf[33];
        auto const compact_sv = mpt::compact_encode(
            compact_buf, mpt::NibblesView{leaf_path}, /*terminating=*/true);

        byte_string const encoded_acct = rlp::encode_account(acct, NULL_ROOT);
        byte_string const leaf_rlp = rlp::encode_list2(
            rlp::encode_string2(compact_sv),
            rlp::encode_string2(
                byte_string_view{encoded_acct.data(), encoded_acct.size()}));

        return db_from_rlp_node(leaf_rlp);
    }

    constexpr auto ADDR_X = 0x00000000000000000000000000000000deadbeef_address;
    constexpr auto ADDR_Y = 0x000000000000000000000000000000000baddcaf_address;
    constexpr auto ADDR_Z = 0xcafef00dcafef00dcafef00dcafef00dcafef00d_address;

    constexpr auto SLOT_1 =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto SLOT_2 =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    constexpr auto VAL_1 =
        0x000000000000000000000000000000000000000000000000000000000000abcd_bytes32;
    constexpr auto VAL_2 =
        0x000000000000000000000000000000000000000000000000000000000000beef_bytes32;
} // namespace

TEST(ParseExecutionWitness, ValidMinimalWitness)
{
    auto const w = make_minimal_witness(PRE_ROOT, POST_ROOT);
    auto const result = parse_execution_witness(w);
    ASSERT_FALSE(result.has_error());
    EXPECT_EQ(result.value().pre_state_root, PRE_ROOT);
    EXPECT_EQ(result.value().post_state_root, POST_ROOT);
    EXPECT_TRUE(result.value().encoded_nodes.empty());
    EXPECT_TRUE(result.value().encoded_codes.empty());
    EXPECT_TRUE(result.value().encoded_headers.empty());
}

TEST(ParseExecutionWitness, EmptyInput)
{
    auto const result = parse_execution_witness({});
    EXPECT_TRUE(result.has_error());
}

TEST(ParseExecutionWitness, OuterTypeNotList)
{
    // A single empty-string byte (0x80) is not a list.
    byte_string const bad{static_cast<unsigned char>(0x80)};
    auto const result = parse_execution_witness(bad);
    EXPECT_TRUE(result.has_error());
}

TEST(ParseExecutionWitness, Truncated)
{
    auto w = make_minimal_witness(PRE_ROOT, POST_ROOT);
    w.resize(w.size() - 5);
    auto const result = parse_execution_witness(w);
    EXPECT_TRUE(result.has_error());
}

TEST(ParseExecutionWitness, PreRootWrongLength)
{
    // Replace the 32-byte pre_state_root item with a 16-byte one so that
    // decode_byte_string_fixed<32> returns ArrayLengthUnexpected.
    byte_string const w = rlp::encode_list2(
        rlp::encode_string2({}),
        rlp::encode_string2(
            byte_string_view{PRE_ROOT.bytes, 16}), // 16 bytes, not 32
        rlp::encode_string2(byte_string_view{POST_ROOT.bytes, 32}),
        byte_string{static_cast<unsigned char>(0xc0)},
        byte_string{static_cast<unsigned char>(0xc0)},
        byte_string{static_cast<unsigned char>(0xc0)},
        byte_string{static_cast<unsigned char>(0xc0)});
    auto const result = parse_execution_witness(w);
    EXPECT_TRUE(result.has_error());
}

TEST(StorageLeafValue, DecodeZeroValue)
{
    // rlp(uint256(0)) = 0x80 (empty string), representing the zero storage
    // value.
    NodeIndex nodes{};
    byte_string const zero_rlp{static_cast<unsigned char>(0x80)};
    byte_string_view enc{zero_rlp.data(), zero_rlp.size()};
    auto const result = StorageLeafValue::decode(enc, nodes);
    ASSERT_FALSE(result.has_error());
    EXPECT_EQ(result.value().value, bytes32_t{});
}

TEST(StorageLeafValue, DecodeEncodeRoundtrip)
{
    // Seed with a fixed value so the test is deterministic.
    std::mt19937_64 rng{0xc0ffee'dead'beef'13ULL};
    std::uniform_int_distribution<unsigned int> byte_dist{0, 255};

    NodeIndex nodes{};

    for (int i = 0; i < 10000; ++i) {
        bytes32_t val{};
        std::generate(std::begin(val.bytes), std::end(val.bytes), [&] {
            return static_cast<uint8_t>(byte_dist(rng));
        });
        storage_leaf_roundtrip(val, nodes, "iteration " + std::to_string(i));
    }
}

TEST(StorageLeafValue, DecodeEncodeRoundtrip_ExtremeValues)
{
    NodeIndex nodes{};

    bytes32_t all_zeros{};
    storage_leaf_roundtrip(all_zeros, nodes, "all zeros");

    bytes32_t all_ffs{};
    std::fill(
        std::begin(all_ffs.bytes), std::end(all_ffs.bytes), uint8_t{0xff});
    storage_leaf_roundtrip(all_ffs, nodes, "all 0xFF");
}

TEST(StorageLeafValue, DecodeTooLong)
{
    // rlp(33 bytes) is a string with a 33-byte payload — one byte over
    // bytes32_t capacity.
    byte_string const overlong =
        rlp::encode_string2(byte_string(33, static_cast<unsigned char>(0xff)));
    NodeIndex nodes{};
    byte_string_view enc{overlong.data(), overlong.size()};
    auto const result = StorageLeafValue::decode(enc, nodes);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooLong);
}

TEST(AccountLeafValue, DecodeEncodeRoundtrip_EmptyStorage)
{
    constexpr auto code_hash =
        0xabcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890_bytes32;
    Account const acct{.balance = 99999, .code_hash = code_hash, .nonce = 7};
    byte_string const encoded_acct = rlp::encode_account(acct, NULL_ROOT);

    NodeIndex nodes{};
    byte_string_view enc{encoded_acct};
    auto const decoded = AccountLeafValue::decode(enc, nodes);
    ASSERT_FALSE(decoded.has_error());

    auto const &decoded_acct = decoded.value();
    EXPECT_EQ(decoded_acct.account.nonce, acct.nonce);
    EXPECT_EQ(decoded_acct.account.balance, acct.balance);
    EXPECT_EQ(decoded_acct.account.code_hash, code_hash);

    // NULL_ROOT storage is represented as nullptr (empty trie), not HashStub.
    EXPECT_EQ(decoded_acct.storage, nullptr);

    EXPECT_EQ(AccountLeafValue::encode(decoded_acct), encoded_acct);
}

TEST(PartialTrieDb, StateRoot_HashStubWhenRootAbsentFromNodeIndex)
{
    // When pre_state_root is not present in the node index the root remains a
    // HashStub, and state_root() must return the original hash unchanged.
    constexpr auto sentinel =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_bytes32;

    auto result =
        PartialTrieDb<NoopAccessTracker>::from_reth_witness(sentinel, {}, {});
    ASSERT_FALSE(result.has_error());
    EXPECT_EQ(result.value().state_root(), sentinel);
}

TEST(PartialTrieDb, StateRoot_SingleLeafRoundtrip)
{
    // Build a single-account leaf node manually, then verify that
    // state_root() re-encodes and re-hashes it to the same value.

    // Dummy leaf path: two nibbles [0xA, 0xB] (even length, so compact prefix =
    // 0x20).
    mpt::Nibbles path{2};
    path.set(0, 0xA);
    path.set(1, 0xB);

    unsigned char compact_buf[33];
    auto const compact_sv = mpt::compact_encode(
        compact_buf, mpt::NibblesView{path}, /*terminating=*/true);
    // compact_sv == { 0x20, 0xAB }

    AccountLeafValue const val{.account = {.nonce = 1}};
    byte_string const encoded_val = AccountLeafValue::encode(val);

    byte_string const leaf_rlp = rlp::encode_list2(
        rlp::encode_string2(compact_sv),
        rlp::encode_string2(
            byte_string_view{encoded_val.data(), encoded_val.size()}));

    auto result = db_from_rlp_node(leaf_rlp);
    ASSERT_FALSE(result.has_error());

    bytes32_t const expected_root =
        to_bytes(keccak256(byte_string_view{leaf_rlp.data(), leaf_rlp.size()}));
    EXPECT_EQ(result.value().state_root(), expected_root);
}

TEST(PartialTrieDb, ShortHashReference)
{
    // A branch child that is a 20-byte string (too short for a hash
    // reference, too long for an empty slot) must fail with InputTooShort.
    byte_string const short_hash(20, static_cast<unsigned char>(0xAA));
    byte_string const child_rlp = rlp::encode_string2(
        byte_string_view{short_hash.data(), short_hash.size()});

    byte_string const branch = make_branch_with_child(0, child_rlp);
    auto result = db_from_rlp_node(branch);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooShort);
}

TEST(PartialTrieDb, ShortHashReference_OneByte)
{
    // A single non-zero byte (self-encodes for [0x01..0x7f]) is a 1-byte
    // string — too short for a hash reference.
    byte_string const child_rlp{static_cast<unsigned char>(0x42)};

    byte_string const branch = make_branch_with_child(0, child_rlp);
    auto result = db_from_rlp_node(branch);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooShort);
}

TEST(PartialTrieDb, LongHashReference)
{
    // A branch child that is a 33-byte string (one byte over the expected
    // 32) must fail with InputTooLong.
    byte_string const long_hash(33, static_cast<unsigned char>(0xBB));
    byte_string const child_rlp = rlp::encode_string2(
        byte_string_view{long_hash.data(), long_hash.size()});

    byte_string const branch = make_branch_with_child(0, child_rlp);
    auto result = db_from_rlp_node(branch);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooLong);
}

TEST(PartialTrieDb, OversizedInlineNode)
{
    // An inline (embedded) node must have full RLP encoding < 32 bytes.
    // Build a list whose payload is 31 bytes to trigger InputTooLong.
    byte_string const payload(31, static_cast<unsigned char>(0x00));
    byte_string const child_rlp = rlp::encode_list2(payload);

    byte_string const branch = make_branch_with_child(0, child_rlp);
    auto result = db_from_rlp_node(branch);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooLong);
}

TEST(PartialTrieDb, EmptyInlineNode)
{
    // An empty list (0xc0) has zero-length payload.
    // Decoding should fail with InputTooShort.
    byte_string const child_rlp{static_cast<unsigned char>(0xc0)};

    byte_string const branch = make_branch_with_child(0, child_rlp);
    auto result = db_from_rlp_node(branch);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooShort);
}

TEST(PartialTrieDb, NodeIndexEntryTrailingData)
{
    // When a hash resolves to a node in the index, the raw entry must be
    // exactly one RLP list with no trailing bytes.  Append a spurious byte
    // so that the "!node_enc.empty()" check fires InputTooLong.
    mpt::Nibbles leaf_path{2};
    leaf_path.set(0, 0xA);
    leaf_path.set(1, 0xB);

    unsigned char compact_buf[33];
    auto const compact_sv = mpt::compact_encode(
        compact_buf, mpt::NibblesView{leaf_path}, /*terminating=*/true);

    AccountLeafValue const val{.account = {.nonce = 1}};
    byte_string const encoded_val = AccountLeafValue::encode(val);

    byte_string node_rlp = rlp::encode_list2(
        rlp::encode_string2(compact_sv),
        rlp::encode_string2(
            byte_string_view{encoded_val.data(), encoded_val.size()}));
    node_rlp.push_back(static_cast<unsigned char>(0xFF));

    auto result = db_from_rlp_node(node_rlp);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::InputTooLong);
}

TEST(PartialTrieDb, PathTooLong)
{
    // A leaf whose compact-encoded path decodes to 65 nibbles exceeds the
    // 64-nibble MPT key limit and must fail with PathTooLong.
    mpt::Nibbles path{65};
    for (unsigned i = 0; i < 65; ++i) {
        path.set(i, static_cast<unsigned char>(i % 16));
    }

    unsigned char compact_buf[34];
    auto const compact_sv = mpt::compact_encode(
        compact_buf, mpt::NibblesView{path}, /*terminating=*/true);

    AccountLeafValue const val{.account = {.nonce = 1}};
    byte_string const encoded_val = AccountLeafValue::encode(val);

    byte_string const leaf_rlp = rlp::encode_list2(
        rlp::encode_string2(compact_sv),
        rlp::encode_string2(
            byte_string_view{encoded_val.data(), encoded_val.size()}));

    auto result = db_from_rlp_node(leaf_rlp);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::PathTooLong);
}

TEST(PartialTrieDb, PathTooLongOver255CompactPath)
{
    byte_string compact_key(129, 0x00);
    compact_key[0] = 0x20; // leaf node, even path length
    AccountLeafValue const val{.account = {.nonce = 1}};
    byte_string const encoded_val = AccountLeafValue::encode(val);
    byte_string const leaf_rlp = rlp::encode_list2(
        rlp::encode_string2(
            byte_string_view{compact_key.data(), compact_key.size()}),
        rlp::encode_string2(
            byte_string_view{encoded_val.data(), encoded_val.size()}));
    auto result = db_from_rlp_node(leaf_rlp);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.error(), rlp::DecodeError::PathTooLong);
}

// ---------------------------------------------------------------------------
// Read tests
// ---------------------------------------------------------------------------

TEST(PartialTrieDb, Read_EmptyTrie)
{
    auto db = make_empty_db();
    EXPECT_EQ(db.read_account(ADDR_X), std::nullopt);
    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), bytes32_t{});
}

TEST(PartialTrieDb, Read_LeafWitness_FoundAndAbsent)
{
    Account const acct{.balance = 1234, .nonce = 7};
    auto result = db_from_account(ADDR_X, acct);
    ASSERT_FALSE(result.has_error());
    auto db = std::move(result.value());

    auto const found = db.read_account(ADDR_X);
    ASSERT_TRUE(found.has_value());
    EXPECT_EQ(found->balance, acct.balance);
    EXPECT_EQ(found->nonce, acct.nonce);

    // Different address misses the single leaf — the trie is fully resolved
    // so the lookup terminates with absent (no HashStub on the path).
    EXPECT_EQ(db.read_account(ADDR_Y), std::nullopt);
    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), bytes32_t{});
}

TEST(PartialTrieDb, ReadCode_PresentAndMissing)
{
    byte_string const code1{
        std::initializer_list<unsigned char>{0x60, 0x01, 0x60, 0x02, 0x01}};
    byte_string const code2{std::initializer_list<unsigned char>{0x00}};
    bytes32_t const hash1 = to_bytes(keccak256(code1));
    bytes32_t const hash2 = to_bytes(keccak256(code2));

    byte_string const encoded_codes =
        rlp::encode_string2(byte_string_view{code1.data(), code1.size()}) +
        rlp::encode_string2(byte_string_view{code2.data(), code2.size()});

    auto result = PartialTrieDb<NoopAccessTracker>::from_reth_witness(
        NULL_ROOT,
        {},
        byte_string_view{encoded_codes.data(), encoded_codes.size()});
    ASSERT_FALSE(result.has_error());
    auto db = std::move(result.value());

    auto const ic1 = db.read_code(hash1);
    EXPECT_EQ(
        byte_string_view(ic1->code(), ic1->size()), byte_string_view{code1});

    auto const ic2 = db.read_code(hash2);
    EXPECT_EQ(
        byte_string_view(ic2->code(), ic2->size()), byte_string_view{code2});

    // Missing hash returns an empty intercode rather than asserting.
    constexpr auto missing =
        0xfeedfacefeedfacefeedfacefeedfacefeedfacefeedfacefeedfacefeedface_bytes32;
    auto const ic_missing = db.read_code(missing);
    EXPECT_EQ(ic_missing->size(), 0u);
}

// ---------------------------------------------------------------------------
// Commit tests
// ---------------------------------------------------------------------------

TEST(PartialTrieDb, Commit_InsertSingleAccount)
{
    auto db = make_empty_db();
    Account const acct{.balance = 1'000, .nonce = 3};

    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_X, StateDelta{.account = {std::nullopt, acct}}}});

    EXPECT_EQ(db.read_account(ADDR_X), acct);
    EXPECT_EQ(db.read_account(ADDR_Y), std::nullopt);
    EXPECT_NE(db.state_root(), NULL_ROOT);
    EXPECT_EQ(db.get_block_number(), 1u);
}

TEST(PartialTrieDb, Commit_UpdateExistingAccount)
{
    auto db = make_empty_db();
    Account const acct1{.balance = 100, .nonce = 1};
    Account const acct2{.balance = 200, .nonce = 2};

    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_X, StateDelta{.account = {std::nullopt, acct1}}}});
    bytes32_t const root_after_insert = db.state_root();

    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_X, StateDelta{.account = {acct1, acct2}}}});

    EXPECT_EQ(db.read_account(ADDR_X), acct2);
    EXPECT_NE(db.state_root(), root_after_insert);
    EXPECT_NE(db.state_root(), NULL_ROOT);
}

TEST(PartialTrieDb, Commit_DeleteAccount_LeavesEmptyTrie)
{
    auto db = make_empty_db();
    Account const acct{.balance = 999, .nonce = 5};

    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_X, StateDelta{.account = {std::nullopt, acct}}}});
    ASSERT_NE(db.state_root(), NULL_ROOT);

    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_X, StateDelta{.account = {acct, std::nullopt}}}});

    EXPECT_EQ(db.read_account(ADDR_X), std::nullopt);
    EXPECT_EQ(db.state_root(), NULL_ROOT);
}

TEST(PartialTrieDb, Commit_TwoAccountsThenDeleteOne_BranchCompresses)
{
    auto db = make_empty_db();
    Account const acct_x{.balance = 1, .nonce = 1};
    Account const acct_y{.balance = 2, .nonce = 2};

    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{
            {ADDR_X, StateDelta{.account = {std::nullopt, acct_x}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, acct_y}}}});

    EXPECT_EQ(db.read_account(ADDR_X), acct_x);
    EXPECT_EQ(db.read_account(ADDR_Y), acct_y);
    ASSERT_NE(db.state_root(), NULL_ROOT);

    // Build a fresh single-leaf trie containing only ADDR_Y → acct_y. After
    // deleting ADDR_X from `db`, branch compression must produce the same trie
    // (and therefore the same state_root).
    auto only_y_result = db_from_account(ADDR_Y, acct_y);
    ASSERT_FALSE(only_y_result.has_error());
    bytes32_t const root_only_y = only_y_result.value().state_root();

    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_X, StateDelta{.account = {acct_x, std::nullopt}}}});

    EXPECT_EQ(db.read_account(ADDR_X), std::nullopt);
    EXPECT_EQ(db.read_account(ADDR_Y), acct_y);
    EXPECT_EQ(db.state_root(), root_only_y);
}

TEST(PartialTrieDb, Commit_TouchOnlyIsNoOp)
{
    auto db = make_empty_db();
    Account const acct{.balance = 7, .nonce = 1};
    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_X, StateDelta{.account = {std::nullopt, acct}}}});
    bytes32_t const root_before = db.state_root();

    // {nullopt, nullopt} hits neither the upsert nor the deletion pass — a
    // pure no-op, even for entries that name a present account.
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{
            {ADDR_X, StateDelta{.account = {std::nullopt, std::nullopt}}},
            {ADDR_Y, StateDelta{.account = {std::nullopt, std::nullopt}}}});

    EXPECT_EQ(db.read_account(ADDR_X), acct);
    EXPECT_EQ(db.state_root(), root_before);
}

TEST(PartialTrieDb, Commit_DeleteAbsentAccountIsNoOp)
{
    auto db = make_empty_db();
    Account const acct{.balance = 7, .nonce = 1};
    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_X, StateDelta{.account = {std::nullopt, acct}}}});
    bytes32_t const root_before = db.state_root();

    // ADDR_Y is not in the trie. The pass-2 branch runs trie_delete which
    // returns false for missing keys; state must be unchanged.
    Account const stale{.balance = 99};
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{{ADDR_Y, StateDelta{.account = {stale, std::nullopt}}}});

    EXPECT_EQ(db.read_account(ADDR_X), acct);
    EXPECT_EQ(db.read_account(ADDR_Y), std::nullopt);
    EXPECT_EQ(db.state_root(), root_before);
}

TEST(PartialTrieDb, Commit_StorageInsertReadDelete)
{
    auto db = make_empty_db();
    Account const acct{.balance = 1, .nonce = 1};

    // Insert account with two storage slots.
    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {
                     {SLOT_1, {bytes32_t{}, VAL_1}},
                     {SLOT_2, {bytes32_t{}, VAL_2}}}}}});

    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), VAL_1);
    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_2), VAL_2);

    // Update SLOT_1, delete SLOT_2 in a second commit.
    commit_with(
        db,
        BlockHeader{.number = 2},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {
                     {SLOT_1, {VAL_1, VAL_2}},
                     {SLOT_2, {VAL_2, bytes32_t{}}}}}}});

    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), VAL_2);
    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_2), bytes32_t{});

    // Slot that was never set returns zero (account exists, slot absent).
    constexpr auto SLOT_3 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_3), bytes32_t{});
}

TEST(PartialTrieDb, Commit_StorageZeroToZeroIsNoOp)
{
    auto db = make_empty_db();
    Account const acct{.balance = 1, .nonce = 1};

    // {0, 0} storage delta hits neither the upsert pass (sdelta.second is
    // zero) nor the delete pass (sdelta.first is zero) — pure no-op.
    commit_with(
        db,
        BlockHeader{.number = 1},
        StateDeltas{
            {ADDR_X,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{SLOT_1, {bytes32_t{}, bytes32_t{}}}}}}});

    EXPECT_EQ(db.read_account(ADDR_X), acct);
    EXPECT_EQ(db.read_storage(ADDR_X, Incarnation{0, 0}, SLOT_1), bytes32_t{});
}

TEST(PartialTrieDb, Commit_PopulatesHeaderRoots)
{
    auto db = make_empty_db();

    constexpr auto receipts =
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_bytes32;
    constexpr auto txns =
        0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb_bytes32;
    constexpr auto withdrawals =
        0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc_bytes32;

    commit_with(
        db, BlockHeader{.number = 42}, StateDeltas{}, [&](BlockHeader &h) {
            h.receipts_root = receipts;
            h.transactions_root = txns;
            h.withdrawals_root = withdrawals;
        });

    EXPECT_EQ(db.receipts_root(), receipts);
    EXPECT_EQ(db.transactions_root(), txns);
    ASSERT_TRUE(db.withdrawals_root().has_value());
    EXPECT_EQ(*db.withdrawals_root(), withdrawals);

    // commit_simple-style consumers expect the populated header to be readable
    // back through read_eth_header.
    auto const stored = db.read_eth_header();
    EXPECT_EQ(stored.number, 42u);
    EXPECT_EQ(stored.receipts_root, receipts);
    EXPECT_EQ(stored.transactions_root, txns);
    ASSERT_TRUE(stored.withdrawals_root.has_value());
    EXPECT_EQ(*stored.withdrawals_root, withdrawals);

    EXPECT_EQ(db.get_block_number(), 42u);
}

TEST(PartialTrieDb, SetBlockAndPrefix_UpdatesBlockNumber)
{
    auto db = make_empty_db();
    EXPECT_EQ(db.get_block_number(), 0u);
    db.set_block_and_prefix(99);
    EXPECT_EQ(db.get_block_number(), 99u);
}

TEST(PartialTrieDb, Commit_StateRootMatchesIndependentlyEncodedTrie)
{
    // Round-trip check: committing one account into an empty trie should yield
    // the same state_root as building a single-leaf trie directly from a
    // synthetic witness.
    auto live = make_empty_db();
    Account const acct{.balance = 0xdeadbeef, .nonce = 12};
    commit_with(
        live,
        BlockHeader{.number = 1},
        StateDeltas{{ADDR_Z, StateDelta{.account = {std::nullopt, acct}}}});

    auto reference_result = db_from_account(ADDR_Z, acct);
    ASSERT_FALSE(reference_result.has_error());
    EXPECT_EQ(live.state_root(), reference_result.value().state_root());
}
