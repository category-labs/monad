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

// The anchor, in two layers, because neither catches what the other does.
//
// The pinned roots below were computed from the MerkleTreeLib rule by an
// implementation outside this tree; pinning roots this code produced would be a
// test that agrees with whatever the code does. The proof round-trip needs no
// external vector and is the only check that exercises the odd-node promotion
// from the PROOF side -- which is the side the L1 contract runs.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/namespace_anchor.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <iterator>
#include <utility>
#include <vector>

using namespace monad;

namespace
{
    constexpr auto SPOKE = 0x00000000000000000000000000000000cafef00d_address;
    constexpr auto OTHER = 0x000000000000000000000000000000000baddcaf_address;

    // Big-endian, because the pinned roots below were computed from
    // big-endian leaves. to_bytes(uint256_t) would be a bare bit_cast and so
    // little-endian on this target -- a different leaf set, and every pinned
    // root would miss.
    std::vector<bytes32_t> ramp(size_t const n)
    {
        std::vector<bytes32_t> v;
        v.reserve(n);
        for (size_t i = 0; i < n; ++i) {
            v.push_back(store_be_as<bytes32_t>(uint256_t{i + 1}));
        }
        return v;
    }

    // A restatement of MerkleTreeLib._hashPair, independent of the one in
    // namespace_anchor.cpp: keccak of the pair in ascending order.
    bytes32_t hash_pair(bytes32_t const &a, bytes32_t const &b)
    {
        unsigned char buf[64];
        bool const swapped = b < a;
        std::memcpy(buf, (swapped ? b : a).bytes, 32);
        std::memcpy(buf + 32, (swapped ? a : b).bytes, 32);
        return to_bytes(keccak256(buf));
    }

    std::vector<bytes32_t> next_layer(std::vector<bytes32_t> const &layer)
    {
        std::vector<bytes32_t> next;
        size_t const n = layer.size();
        for (size_t i = 0; i < n / 2; ++i) {
            next.push_back(hash_pair(layer[2 * i], layer[2 * i + 1]));
        }
        if (n % 2 == 1) {
            next.push_back(layer[n - 1]);
        }
        return next;
    }

    /// The merkle path for `index`, built the way MerkleTreeLib.getProof does.
    std::vector<bytes32_t>
    make_proof(std::vector<bytes32_t> const &leaves, size_t index)
    {
        std::vector<bytes32_t> proof;
        auto layer = leaves;
        while (layer.size() > 1) {
            size_t const sibling = index ^ 1u;
            if (sibling < layer.size()) {
                proof.push_back(layer[sibling]);
            }
            index /= 2;
            layer = next_layer(layer);
        }
        return proof;
    }

    /// OpenZeppelin MerkleProof.processProof.
    bytes32_t process_proof(bytes32_t leaf, std::vector<bytes32_t> const &proof)
    {
        for (auto const &p : proof) {
            leaf = hash_pair(leaf, p);
        }
        return leaf;
    }

    Receipt::Log make_message_log(
        Address const &address, bytes32_t const &topic0,
        bytes32_t const &message_hash, uint64_t const nonce,
        byte_string const &payload)
    {
        byte_string data;
        // ABI words are big-endian, so store_be_as and not to_bytes -- which
        // is a bare bit_cast and would build the head words backwards.
        auto const push_word = [&data](uint256_t const &v) {
            auto const w = store_be_as<bytes32_t>(v);
            data.append(w.bytes, w.bytes + 32);
        };
        push_word(uint256_t{NAMESPACE_LOG_DATA_OFFSET}); // offset of the tail
        push_word(uint256_t{nonce});
        data.append(message_hash.bytes, message_hash.bytes + 32);
        push_word(uint256_t{payload.size()});
        data.append(payload.begin(), payload.end());
        data.resize(((data.size() + 31) / 32) * 32); // pad the tail

        Receipt::Log log{};
        log.address = address;
        log.topics = {topic0, bytes32_t{}, bytes32_t{}}; // from, to
        log.data = data;
        return log;
    }

    Receipt make_receipt(std::vector<Receipt::Log> logs)
    {
        Receipt r{};
        for (auto const &l : logs) {
            r.add_log(l);
        }
        return r;
    }
}

// ---------------------------------------------------------------------------
// The merkle rule
// ---------------------------------------------------------------------------

TEST(SortedPairMerkleRoot, PinnedRoots)
{
    bytes32_t const want[] = {
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32,
        0xe90b7bceb6e7df5418fb78d8ee546e97c83a08bbccc01a0644d599ccd2a7c2e0_bytes32,
        0x9b0225f2c6f59eeaf8302811ea290e95258763189b82dc033158e99a6ef45a87_bytes32,
        0x0c48ddc2b8d6d066c52fc608d4d0254f418bea6cd8424fe95390ac87323f9c9f_bytes32,
        0x3856185f708a95a4cef51f6538ed3ea849702a46e020430070ac99c94a831c58_bytes32,
        0x26640d7b4dfe8c87859c9cbe9a90ae76d9df382318098615363e336596d4f141_bytes32,
        0xaab02f3db9c93e147ef0d40da39365ede78ea78fa103e04807c407977a9cd0ff_bytes32,
        0xca06f8324669a77a3ef9a7bcf15421d7bb5618a79dbe5590117ba5f5a4e72bc1_bytes32,
        0xeaa579846af71a39e8280f33a4528ccc7030237aa05632dc6f644e220da4fd16_bytes32,
    };
    for (size_t n = 1; n <= std::size(want); ++n) {
        auto leaves = ramp(n);
        EXPECT_EQ(sorted_pair_merkle_root(leaves), want[n - 1]) << "n = " << n;
    }
}

// finalizeNamespaceMessages returns bytes32(0) when nothing is pending; it is
// MerkleTreeLib.root, not the contract, that reverts on an empty array.
TEST(SortedPairMerkleRoot, EmptyIsZero)
{
    std::vector<bytes32_t> none;
    EXPECT_EQ(sorted_pair_merkle_root(none), bytes32_t{});
}

TEST(SortedPairMerkleRoot, SingleLeafIsItsOwnRoot)
{
    auto one = ramp(1);
    EXPECT_EQ(
        sorted_pair_merkle_root(one), store_be_as<bytes32_t>(uint256_t{1}));
}

// Every leaf's path must fold back to the root under OpenZeppelin's rule. This
// is what the L1 runs, and n = 3, 5, 7, 9... are where promotion lands at
// different depths.
TEST(SortedPairMerkleRoot, EveryProofVerifies)
{
    for (size_t n = 1; n <= 17; ++n) {
        auto const leaves = ramp(n);
        auto scratch = leaves;
        auto const root = sorted_pair_merkle_root(scratch);
        for (size_t i = 0; i < n; ++i) {
            EXPECT_EQ(process_proof(leaves[i], make_proof(leaves, i)), root)
                << "n = " << n << ", leaf " << i;
        }
    }
}

// Ordering is part of the commitment: the same messages pushed in another order
// anchor to something else.
TEST(SortedPairMerkleRoot, LeafOrderMatters)
{
    auto a = ramp(3);
    auto b = ramp(3);
    std::swap(b[0], b[2]);
    EXPECT_NE(sorted_pair_merkle_root(a), sorted_pair_merkle_root(b));
}

// ---------------------------------------------------------------------------
// The harvest
// ---------------------------------------------------------------------------

TEST(CollectNamespaceMessages, GathersInLogOrderAcrossReceipts)
{
    auto const h1 = store_be_as<bytes32_t>(uint256_t{0x11});
    auto const h2 = store_be_as<bytes32_t>(uint256_t{0x22});
    auto const h3 = store_be_as<bytes32_t>(uint256_t{0x33});
    std::vector<Receipt> const receipts{
        make_receipt(
            {make_message_log(
                 SPOKE, NAMESPACE_MESSAGE_RECORDED_TOPIC, h1, 0, {}),
             make_message_log(
                 SPOKE, NAMESPACE_MESSAGE_RECORDED_TOPIC, h2, 1, {1, 2, 3})}),
        make_receipt({make_message_log(
            SPOKE,
            NAMESPACE_MESSAGE_RECORDED_TOPIC,
            h3,
            2,
            byte_string(40, 7))}),
    };
    auto const got = collect_namespace_messages(receipts, SPOKE);
    ASSERT_FALSE(got.has_error());
    EXPECT_EQ(got.value(), (std::vector<bytes32_t>{h1, h2, h3}));
}

TEST(CollectNamespaceMessages, EmptyBlockGivesNoLeaves)
{
    EXPECT_TRUE(collect_namespace_messages({}, SPOKE).value().empty());
    std::vector<Receipt> const quiet{make_receipt({})};
    EXPECT_TRUE(collect_namespace_messages(quiet, SPOKE).value().empty());
}

// Anything that is not this contract's event is not our business.
TEST(CollectNamespaceMessages, IgnoresOtherLogs)
{
    auto const h = store_be_as<bytes32_t>(uint256_t{0x44});
    Receipt::Log no_topics{};
    no_topics.address = SPOKE;
    std::vector<Receipt> const receipts{make_receipt({
        make_message_log(OTHER, NAMESPACE_MESSAGE_RECORDED_TOPIC, h, 0, {}),
        make_message_log(
            SPOKE, store_be_as<bytes32_t>(uint256_t{0xdead}), h, 0, {}),
        no_topics,
    })};
    auto const got = collect_namespace_messages(receipts, SPOKE);
    ASSERT_FALSE(got.has_error());
    EXPECT_TRUE(got.value().empty());
}

// A log that claims to be ours and does not decode means the deployed contract
// changed. Skipping it would give a well-formed anchor over the wrong leaves --
// which the hub would accept -- so it fails the block.
TEST(CollectNamespaceMessages, RejectsMalformedOwnLogs)
{
    auto const h = store_be_as<bytes32_t>(uint256_t{0x55});
    auto const good =
        make_message_log(SPOKE, NAMESPACE_MESSAGE_RECORDED_TOPIC, h, 0, {});

    auto reject = [](Receipt::Log log, char const *what) {
        std::vector<Receipt> const receipts{make_receipt({log})};
        auto const got = collect_namespace_messages(receipts, SPOKE);
        EXPECT_TRUE(got.has_error()) << what;
        if (got.has_error()) {
            EXPECT_EQ(got.error(), BlockError::InvalidNamespaceLog) << what;
        }
    };

    { // two topics: the parameter list is not what this code decodes
        auto l = good;
        l.topics.pop_back();
        reject(l, "topic count");
    }
    { // four topics
        auto l = good;
        l.topics.push_back(bytes32_t{});
        reject(l, "extra topic");
    }
    { // shorter than three head words plus a length word
        auto l = good;
        l.data.resize(NAMESPACE_LOG_MIN_SIZE - 32);
        reject(l, "truncated data");
    }
    { // a head offset Solidity would never emit for this signature
        auto l = good;
        l.data[31] = 0x40;
        reject(l, "head offset");
    }
    { // a declared tail length its own data section cannot hold
        auto l = good;
        l.data[NAMESPACE_LOG_HEAD_WORDS * 32 + 31] = 0xff;
        reject(l, "declared tail length");
    }
}

// ---------------------------------------------------------------------------
// The pending array's storage layout
// ---------------------------------------------------------------------------

// Solidity puts element i of a dynamic array at keccak256(slot) + i. Pinned
// against an independent computation, because getting this wrong would clear
// somebody else's storage.
TEST(NamespacePendingElementKey, MatchesSolidityLayout)
{
    EXPECT_EQ(
        namespace_pending_element_key(1, 0),
        0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6_bytes32);
    EXPECT_EQ(
        namespace_pending_element_key(1, 1),
        0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf7_bytes32);
    EXPECT_EQ(
        namespace_pending_element_key(1, 3),
        0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf9_bytes32);
    EXPECT_EQ(
        namespace_pending_element_key(2, 0),
        0x405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace_bytes32);
}
