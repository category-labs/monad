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

#include <zkvm/test/corpus/corpus_builder.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <category/vm/code.hpp>
#include <functional>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr auto KEY_A =
        0x0000000000000000000000000000000000000000000000000000000000000a11_bytes32;
    constexpr auto KEY_B =
        0x0000000000000000000000000000000000000000000000000000000000000b22_bytes32;

    /// The operator secret whose public half these tests are configured with.
    /// Ignored in a plaintext build; in an L2 one the builder checks it
    /// against the compiled MONAD_ZKVM_L2_OPERATOR_PK_X and aborts on a
    /// mismatch, so a tree configured with another key fails here rather than
    /// producing a corpus nothing can decrypt.
    constexpr auto OPERATOR_SK =
        0x00000000000000000000000000000000000000000000000000000000cafef00d_bytes32;

    corpus::CorpusBuilder make_builder(std::function<void(State &)> const &g)
    {
        return corpus::CorpusBuilder{g, OPERATOR_SK};
    }
}

TEST(CorpusSigner, SenderRecovers)
{
    Transaction tx{
        .nonce = 7,
        .max_fee_per_gas = 1,
        .gas_limit = 21000,
        .value = 5,
        .to = corpus::address_of(KEY_B),
        .type = TransactionType::eip1559};
    tx.sc.chain_id = 1;
    corpus::sign_transaction(tx, KEY_A);

    auto const sender = recover_sender(tx);
    ASSERT_TRUE(sender.has_value());
    EXPECT_EQ(sender.value(), corpus::address_of(KEY_A));
}

TEST(CorpusBuilder, OneTransferBlockRoundTrips)
{
    auto b = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
    });

    corpus::BlockSpec spec;
    Transaction tx{
        .max_fee_per_gas = 0,
        .gas_limit = 21000,
        .value = 1000,
        .to = corpus::address_of(KEY_B),
        .type = TransactionType::eip1559};
    tx.sc.chain_id = 1;
    spec.txs.push_back(tx);
    spec.keys.push_back(KEY_A);

    auto const e = b.add_block(std::move(spec));
    EXPECT_FALSE(e.witness.empty());
    EXPECT_NE(e.pre_root, e.post_root);
    EXPECT_EQ(e.header.gas_used, 21000u);
}

namespace
{
    /// Load the emitted witness the way the guest does: the blob names its own
    /// root, so nothing external is needed to open it.
    PartialTrieDb guest_view(byte_string const &witness)
    {
#ifdef MONAD_ZKVM_L2
        // Seven fields here and six otherwise, and each shape rejects the
        // other loudly rather than silently mis-parsing -- which is the whole
        // argument for there being no version byte.
        auto parsed = parse_execution_witness_l2(witness);
        MONAD_ASSERT(parsed.has_value());
        auto const &w = parsed.value().base;
#else
        auto parsed = parse_execution_witness(witness);
        MONAD_ASSERT(parsed.has_value());
        auto const &w = parsed.value();
#endif

        CodeIndex codes;
        byte_string_view rest = w.encoded_codes;
        while (!rest.empty()) {
            auto const item = rlp::parse_string_metadata(rest);
            MONAD_ASSERT(item.has_value());
            codes.emplace(
                to_bytes(keccak256(item.value())),
                vm::make_shared_intercode(item.value()));
        }
        return PartialTrieDb{
            mpt::OffsetTrie{w.encoded_nodes}, std::move(codes)};
    }
}

// ---------------------------------------------------------------------------
// The milestone, and it is not circular: this side computed the root with
// TrieDb, the node's backend; PartialTrieDb recomputes it with OffsetTrie from
// the blob. Two implementations of the same trie.
// ---------------------------------------------------------------------------

TEST(CorpusBuilder, WitnessCarriesThePreState)
{
    auto b = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
        s.add_to_balance(corpus::address_of(KEY_B), 500000000000000000_u256);
    });

    corpus::BlockSpec spec;
    Transaction tx{
        .max_fee_per_gas = 0,
        .gas_limit = 21000,
        .value = 1000,
        .to = corpus::address_of(KEY_B),
        .type = TransactionType::eip1559};
    tx.sc.chain_id = 1;
    spec.txs.push_back(tx);
    spec.keys.push_back(KEY_A);

    auto const e = b.add_block(std::move(spec));

    auto gv = guest_view(e.witness);
    EXPECT_EQ(gv.state_root(), e.pre_root);
}

TEST(CorpusBuilder, TheBlockInTheWitnessIsTheBlockThatWasSealed)
{
    auto b = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
    });

    corpus::BlockSpec spec;
    Transaction tx{
        .max_fee_per_gas = 0,
        .gas_limit = 21000,
        .value = 7,
        .to = corpus::address_of(KEY_B),
        .type = TransactionType::eip1559};
    tx.sc.chain_id = 1;
    spec.txs.push_back(tx);
    spec.keys.push_back(KEY_A);

    auto const e = b.add_block(std::move(spec));

#ifdef MONAD_ZKVM_L2
    auto parsed = parse_execution_witness_l2(e.witness);
    ASSERT_TRUE(parsed.has_value());
    byte_string_view block_view = parsed.value().base.block_rlp;
    // Only the header: the transactions list holds ciphertexts, which
    // rlp::decode_block would try to read as transactions.
    auto payload = rlp::parse_list_metadata(block_view);
    ASSERT_TRUE(payload.has_value());
    byte_string_view body = payload.value();
    auto header = rlp::decode_block_header(body);
    ASSERT_TRUE(header.has_value());
    EXPECT_EQ(
        to_bytes(keccak256(rlp::encode_block_header(header.value()))),
        e.block_hash);
    EXPECT_EQ(header.value().state_root, e.post_root);
#else
    auto parsed = parse_execution_witness(e.witness);
    ASSERT_TRUE(parsed.has_value());
    byte_string_view block_view = parsed.value().block_rlp;
    auto decoded = rlp::decode_block(block_view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(
        to_bytes(keccak256(rlp::encode_block_header(decoded.value().header))),
        e.block_hash);
    EXPECT_EQ(decoded.value().header.state_root, e.post_root);
#endif
}

// ---------------------------------------------------------------------------
// Field [3] is the one that binds the ancestor list to the blob: the newest
// ancestor must carry the pre-state root the blob was generated against. Get
// it wrong and the guest aborts with nothing in the failure naming the cause.
// ---------------------------------------------------------------------------

TEST(CorpusBuilder, AncestorHeadersChainToTheParentAndThePreState)
{
    auto b = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
    });

    corpus::Emitted last{};
    for (int i = 0; i < 3; ++i) {
        corpus::BlockSpec spec;
        Transaction tx{
            .max_fee_per_gas = 0,
            .gas_limit = 21000,
            .value = 1,
            .to = corpus::address_of(KEY_B),
            .type = TransactionType::eip1559};
        tx.sc.chain_id = 1;
        spec.txs.push_back(tx);
        spec.keys.push_back(KEY_A);
        last = b.add_block(std::move(spec));
    }

#ifdef MONAD_ZKVM_L2
    auto parsed = parse_execution_witness_l2(last.witness);
    ASSERT_TRUE(parsed.has_value());
    byte_string_view rest = parsed.value().base.encoded_headers;
#else
    auto parsed = parse_execution_witness(last.witness);
    ASSERT_TRUE(parsed.has_value());
    byte_string_view rest = parsed.value().encoded_headers;
#endif

    std::vector<BlockHeader> ancestors;
    while (!rest.empty()) {
        auto item = rlp::parse_string_metadata(rest);
        ASSERT_TRUE(item.has_value());
        byte_string_view hv = item.value();
        auto h = rlp::decode_block_header(hv);
        ASSERT_TRUE(h.has_value());
        ancestors.push_back(h.value());
    }
    ASSERT_FALSE(ancestors.empty());

    for (size_t i = 1; i < ancestors.size(); ++i) {
        EXPECT_EQ(ancestors[i].number, ancestors[i - 1].number + 1);
        EXPECT_EQ(
            ancestors[i].parent_hash,
            to_bytes(keccak256(rlp::encode_block_header(ancestors[i - 1]))));
    }
    EXPECT_EQ(
        to_bytes(keccak256(rlp::encode_block_header(ancestors.back()))),
        last.header.parent_hash);
    EXPECT_EQ(ancestors.back().state_root, last.pre_root);
}

// ---------------------------------------------------------------------------
// Every scenario, through the same property. This is what keeps a change to
// the generator or to the trie from going unnoticed: the pre-state root the
// guest's OffsetTrie derives from the blob has to be the one this side's
// TrieDb had, on blocks that deploy, log, revert, self-destruct and carry
// three transaction types.
// ---------------------------------------------------------------------------

TEST(CorpusScenarios, EveryBlockRoundTripsThroughTheGuestTrie)
{
    bytes32_t seed{};
    seed.bytes[31] = 1;

    for (auto const &sc : corpus::all_scenarios(seed)) {
        auto b = make_builder(sc.genesis);
        for (auto &spec : sc.blocks(b)) {
            auto const e = b.add_block(std::move(spec));
            SCOPED_TRACE(sc.name + " " + std::to_string(e.header.number));

            auto gv = guest_view(e.witness);
            EXPECT_EQ(gv.state_root(), e.pre_root);
            EXPECT_FALSE(e.receipts.empty());
        }
    }
}

// ---------------------------------------------------------------------------
// The spoke is in the corpus for one reason: the L2 anchor harvests
// NamespaceMessageRecorded out of receipts. If the deployment silently failed
// -- wrong constructor encoding, out of gas -- the block would still execute
// and still round-trip, and the logs simply would not be there. So check the
// logs, not the roots.
// ---------------------------------------------------------------------------

TEST(CorpusScenarios, TheSpokeEmitsHarvestableMessages)
{
    static constexpr auto TOPIC0 = abi_encode_event_signature(
        "NamespaceMessageRecorded(address,address,bytes,uint256,bytes32)");

    bytes32_t seed{};
    seed.bytes[31] = 1;

    bool found_scenario = false;
    for (auto const &sc : corpus::all_scenarios(seed)) {
        if (sc.name != "spoke") {
            continue;
        }
        found_scenario = true;
        auto b = make_builder(sc.genesis);
        auto specs = sc.blocks(b);
        ASSERT_EQ(specs.size(), 2u);

        // Block 1 deploys. A CREATE that ran out of gas still produces a
        // receipt, so check the status as well as the code.
        auto const deploy = b.add_block(std::move(specs[0]));
        ASSERT_EQ(deploy.receipts.size(), 1u);
        EXPECT_EQ(deploy.receipts[0].status, 1u);

        // Block 2 sends three messages.
        auto const send = b.add_block(std::move(specs[1]));
        ASSERT_EQ(send.receipts.size(), 3u);

        unsigned logs = 0;
        for (auto const &r : send.receipts) {
            EXPECT_EQ(r.status, 1u);
            for (auto const &log : r.logs) {
                ASSERT_FALSE(log.topics.empty());
                if (log.topics[0] == TOPIC0) {
                    // from and to are indexed, so three topics, and the data
                    // section carries the tail offset, the nonce and the
                    // message hash before the payload.
                    EXPECT_EQ(log.topics.size(), 3u);
                    EXPECT_GE(log.data.size(), 128u);
                    ++logs;
                }
            }
        }
        EXPECT_EQ(logs, 3u);
    }
    EXPECT_TRUE(found_scenario);
}
