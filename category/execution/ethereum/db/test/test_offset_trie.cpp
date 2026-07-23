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

// Offset-format trie (wip_WITNESS_OFFSET_FORMAT.md): verify + views + open +
// lookup. Builds a small blob by hand (no encoder yet) and reads it back.

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/nibble.h>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <cstring>
#include <vector>

using namespace monad;
using namespace monad::mpt;

namespace
{
    mpt::Nibbles nibs_to_path(std::vector<uint8_t> const &nibs)
    {
        mpt::Nibbles p{nibs.size()};
        for (unsigned i = 0; i < nibs.size(); ++i) {
            p.set(i, nibs[i]);
        }
        return p;
    }

    // Builds an offset-format blob (§3/§4) for tests, post-order so every child
    // offset precedes its parent. Node bytes come from the production append_*
    // writers, so the node layout has a single source of truth; only the header
    // and the offset bookkeeping live here.
    struct BlobBuilder
    {
        byte_string buf;

        BlobBuilder()
            : buf{'M', 'Z', 'W', 0x01, 0, 0, 0, 0}
        {
        }

        uint32_t here() const
        {
            return static_cast<uint32_t>(buf.size());
        }

        uint32_t storage_leaf(std::vector<uint8_t> const &nibs, bytes32_t val)
        {
            uint32_t const off = here();
            mpt::Nibbles const path = nibs_to_path(nibs);
            append_storage(buf, mpt::NibblesView{path}, val);
            return off;
        }

        uint32_t digest(bytes32_t h)
        {
            uint32_t const off = here();
            append_digest(buf, h);
            return off;
        }

        uint32_t branch(std::array<uint32_t, 16> const &ch)
        {
            uint32_t const off = here();
            std::array<NodeId, 16> children{};
            for (unsigned i = 0; i < 16; ++i) {
                children[i] = NodeId{ch[i]};
            }
            append_branch(buf, children);
            return off;
        }

        byte_string finalize(uint32_t const root_off)
        {
            // LE, matching read_node_id (both sides assert a little-endian
            // host)
            std::memcpy(buf.data() + 4, &root_off, sizeof(root_off));
            return buf;
        }
    };

    // ── independent RLP oracle (allocating encode2 path) ────────────────────
    bytes32_t oracle_hash(byte_string const &rlp)
    {
        return to_bytes(keccak256(byte_string_view{rlp}));
    }

    // canonical RLP of a storage leaf: list[ compact(path,leaf), string(rlp(v))
    // ]
    byte_string
    oracle_storage_leaf(std::vector<uint8_t> const &nibs, bytes32_t v)
    {
        mpt::Nibbles const p = nibs_to_path(nibs);
        unsigned char cbuf[33];
        auto const compact =
            mpt::compact_encode(cbuf, mpt::NibblesView{p}, /*term=*/true);
        byte_string const trie_val = rlp::encode_string2(
            rlp::zeroless_view(to_byte_string_view(v.bytes)));
        return rlp::encode_list2(
            rlp::encode_string2(compact),
            rlp::encode_string2(byte_string_view{trie_val}));
    }

    // parent-facing reference of a child node's RLP
    byte_string oracle_ref(byte_string const &node_rlp)
    {
        if (node_rlp.size() < 32) {
            return node_rlp; // inline
        }
        return rlp::encode_string2(
            byte_string_view{oracle_hash(node_rlp).bytes, 32});
    }

    // canonical RLP of an account leaf:
    // list[ compact(path,leaf), string(acct) ]
    byte_string oracle_account_leaf(
        mpt::NibblesView const path, byte_string const &acct_rlp)
    {
        unsigned char cbuf[33];
        auto const compact = mpt::compact_encode(cbuf, path, /*term=*/true);
        return rlp::encode_list2(
            rlp::encode_string2(compact),
            rlp::encode_string2(byte_string_view{acct_rlp}));
    }

    // ── helpers for building a trie from scratch via OffsetTrie mutation
    // ────── NibblesView over a 32-byte key (64 nibbles, MSB-first).
    mpt::NibblesView key_view(bytes32_t const &k)
    {
        return mpt::NibblesView{byte_string_view{k.bytes, sizeof(k.bytes)}};
    }

    // The 64 nibbles of a 32-byte key, as the oracle helpers expect them.
    std::vector<uint8_t> key_nibbles(bytes32_t const &k)
    {
        std::vector<uint8_t> n(64);
        for (unsigned i = 0; i < 64; ++i) {
            n[i] = get_nibble(k.bytes, i);
        }
        return n;
    }

    // A 32-byte key from two marker bytes (first/last), so two keys can be made
    // to diverge at nibble 0 by choosing different high nibbles of byte 0.
    bytes32_t make_key(uint8_t const first, uint8_t const last)
    {
        bytes32_t k{};
        k.bytes[0] = first;
        k.bytes[31] = last;
        return k;
    }

    // An empty (root_off == 0) offset-trie blob to build onto.
    byte_string empty_blob()
    {
        BlobBuilder bb;
        return bb.finalize(0);
    }

    // Insert into the account trie, as PartialTrieDb::commit does: an empty
    // trie's root is NULL_ID, so the first leaf becomes the new root. Returns
    // the leaf id + path for the caller to put_acct.
    std::pair<NodeId, mpt::Nibbles>
    upsert_account(OffsetTrie &store, mpt::NibblesView const key)
    {
        auto const res = store.upsert_node(store.root, key);
        if (store.root == NULL_ID) {
            store.root = res.first;
        }
        return res;
    }
}

TEST(OffsetTrie, VerifyOpenViewsFind)
{
    bytes32_t v1{};
    v1.bytes[31] = 0x11;
    bytes32_t hdig{};
    for (auto &b : hdig.bytes) {
        b = 0xab;
    }

    BlobBuilder bb;
    uint32_t const leaf = bb.storage_leaf({0xa}, v1); // key tail = [a]
    uint32_t const dig = bb.digest(hdig);
    std::array<uint32_t, 16> ch{};
    ch[3] = leaf;
    ch[7] = dig;
    uint32_t const br = bb.branch(ch);
    byte_string const blob = bb.finalize(br);

    OffsetTrie const store{blob};
    EXPECT_EQ(static_cast<uint64_t>(store.root), br);

    // match the root branch through the view accessors
    bool const matched = match(
        store.get_current(store.root),
        Cases{
            [&](BranchView b) -> bool {
                EXPECT_EQ(static_cast<uint64_t>(b.child(3)), leaf);
                EXPECT_EQ(static_cast<uint64_t>(b.child(7)), dig);
                EXPECT_EQ(b.child(0), NULL_ID);
                return true;
            },
            [&](auto) -> bool { return false; }});
    EXPECT_TRUE(matched);

    EXPECT_EQ(StorageLeafView{store.get_current(NodeId{leaf})}.value(), v1);
    EXPECT_EQ(DigestView{store.get_current(NodeId{dig})}.hash(), hdig);

    // find the storage leaf by full key [3, a]
    mpt::Nibbles key{2};
    key.set(0, 3);
    key.set(1, 0xa);
    auto const found = store.find_original(store.root, mpt::NibblesView{key});
    EXPECT_EQ(found.tag(), LEAF_STORAGE);
    EXPECT_EQ(StorageLeafView{found}.value(), v1);

    // absent key
    mpt::Nibbles absent{2};
    absent.set(0, 4);
    absent.set(1, 0x0);
    EXPECT_EQ(
        store.find_original(store.root, mpt::NibblesView{absent}).tag(), EMPTY);
}

TEST(OffsetTrieDeathTest, OutOfRangeChildAborts)
{
    BlobBuilder bb;
    uint32_t const leaf = bb.storage_leaf({0xa}, bytes32_t{});
    std::array<uint32_t, 16> ch{};
    ch[3] = leaf;
    ch[7] = 999999; // out-of-range child offset
    uint32_t const br = bb.branch(ch);
    byte_string const blob = bb.finalize(br);
    // priming follows the bad edge into get_original, which aborts.
    EXPECT_DEATH((void)OffsetTrie{blob}, "");
}

TEST(OffsetTrie, HashSingleStorageLeaf)
{
    bytes32_t v{};
    v.bytes[31] = 0x11;
    std::vector<uint8_t> const nibs = {1, 2, 3};

    BlobBuilder bb;
    uint32_t const leaf = bb.storage_leaf(nibs, v);
    byte_string const blob = bb.finalize(leaf);

    OffsetTrie store{blob};
    EXPECT_EQ(store.state_root(), oracle_hash(oracle_storage_leaf(nibs, v)));
}

TEST(OffsetTrie, HashBranchWithDigest)
{
    bytes32_t v1{};
    v1.bytes[31] = 0x11;
    bytes32_t hdig{};
    for (auto &b : hdig.bytes) {
        b = 0xab;
    }

    BlobBuilder bb;
    uint32_t const leaf = bb.storage_leaf({0xa}, v1);
    uint32_t const dig = bb.digest(hdig);
    std::array<uint32_t, 16> ch{};
    ch[3] = leaf;
    ch[7] = dig;
    uint32_t const br = bb.branch(ch);
    byte_string const blob = bb.finalize(br);

    OffsetTrie store{blob};

    // oracle: 16 child refs + empty value, wrapped as a list, then keccak
    byte_string body;
    for (unsigned i = 0; i < 16; ++i) {
        if (i == 3) {
            body += oracle_ref(oracle_storage_leaf({0xa}, v1));
        }
        else if (i == 7) {
            body += rlp::encode_string2(byte_string_view{hdig.bytes, 32});
        }
        else {
            body += rlp::EMPTY_STRING; // 0x80
        }
    }
    body += rlp::EMPTY_STRING; // empty branch value
    bytes32_t const want = oracle_hash(rlp::encode_list2(body));

    EXPECT_EQ(store.state_root(), want);
}

// ── mutation: build the trie from scratch via upsert/erase, check state_root
// against the independent RLP oracle ────────────────────────────────────────

TEST(OffsetTrie, UpsertSingleAccount)
{
    byte_string const blob = empty_blob();
    OffsetTrie store{blob};

    bytes32_t const key = make_key(0x12, 0x34);
    Account acct{};
    acct.balance = 5;
    acct.nonce = 7;

    auto const [leaf, path] = upsert_account(store, key_view(key));
    store.put_acct(leaf, mpt::NibblesView{path}, acct, NULL_ID);

    // sole node: a leaf holding the full key
    byte_string const arlp = rlp::encode_account(acct, NULL_ROOT);
    EXPECT_EQ(
        store.state_root(),
        oracle_hash(oracle_account_leaf(key_view(key), arlp)));
}

TEST(OffsetTrie, UpsertTwoAccountsThenErase)
{
    byte_string const blob = empty_blob();
    OffsetTrie store{blob};

    bytes32_t const ka = make_key(0x0a, 0x11); // nibble 0 = 0x0
    bytes32_t const kb = make_key(0xb0, 0x22); // nibble 0 = 0xb (diverge at 0)
    Account aa{};
    aa.balance = 1;
    Account ab{};
    ab.balance = 2;

    auto const insert = [&](bytes32_t const &k, Account const &a) {
        auto const [leaf, path] = upsert_account(store, key_view(k));
        store.put_acct(leaf, mpt::NibblesView{path}, a, NULL_ID);
    };
    insert(ka, aa);
    insert(kb, ab);

    // oracle: a branch with the two accounts as children (each a leaf over the
    // remaining 63 nibbles), no branch value.
    byte_string const arlp = rlp::encode_account(aa, NULL_ROOT);
    byte_string const brlp = rlp::encode_account(ab, NULL_ROOT);
    byte_string body;
    for (unsigned i = 0; i < 16; ++i) {
        if (i == 0x0) {
            body +=
                oracle_ref(oracle_account_leaf(key_view(ka).substr(1), arlp));
        }
        else if (i == 0xb) {
            body +=
                oracle_ref(oracle_account_leaf(key_view(kb).substr(1), brlp));
        }
        else {
            body += rlp::EMPTY_STRING;
        }
    }
    body += rlp::EMPTY_STRING; // empty branch value
    EXPECT_EQ(store.state_root(), oracle_hash(rlp::encode_list2(body)));

    // erase ka -> the branch collapses back to a single leaf over the full kb
    store.erase_node(store.root, key_view(ka));
    EXPECT_EQ(
        store.state_root(),
        oracle_hash(oracle_account_leaf(key_view(kb), brlp)));
}

TEST(OffsetTrie, UpsertAccountWithStorage)
{
    byte_string const blob = empty_blob();
    OffsetTrie store{blob};

    bytes32_t const akey = make_key(0x12, 0x34);
    bytes32_t const skey = make_key(0x56, 0x78);
    bytes32_t sval{};
    sval.bytes[31] = 0x99;
    Account acct{};
    acct.balance = 3;

    auto const [leaf, apath] = upsert_account(store, key_view(akey));
    auto const [storage, spath] = store.upsert_node(NULL_ID, key_view(skey));
    store.put_storage(storage, mpt::NibblesView{spath}, sval);
    bytes32_t const sroot = store.hash(storage);
    // No root is handed over: the leaf must derive `sroot` from `storage`.
    store.put_acct(leaf, mpt::NibblesView{apath}, acct, storage);

    // storage sub-root is a single storage leaf over the full slot key
    bytes32_t const oracle_sroot =
        oracle_hash(oracle_storage_leaf(key_nibbles(skey), sval));
    EXPECT_EQ(sroot, oracle_sroot);

    byte_string const arlp = rlp::encode_account(acct, oracle_sroot);
    EXPECT_EQ(
        store.state_root(),
        oracle_hash(oracle_account_leaf(key_view(akey), arlp)));
}
