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
#include <zkvm/test/corpus/genesis_bulk.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>
#include <zkvm/test/corpus/witness_stats.hpp>
#include <zkvm/test/corpus/workload.hpp>

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

#include <cmath>
#include <cstring>
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

    /// The blinder secret whose keccak256 these tests are configured with.
    constexpr auto SALT_SECRET =
        0x000000000000000000000000000000000000000000000000000000005a1700d5_bytes32;

    corpus::CorpusBuilder make_builder(std::function<void(State &)> const &g)
    {
        return corpus::CorpusBuilder{g, OPERATOR_SK, SALT_SECRET};
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

#ifdef MONAD_ZKVM_L2
// ---------------------------------------------------------------------------
// The blinder. Two properties, and the second is the one that matters: a
// constant blinder would leave two blocks of identical state publishing the
// same hash, which on a low-volume chain says which blocks did nothing.
// ---------------------------------------------------------------------------

TEST(CorpusBlinder, TheHeaderCarriesThePerBlockBlinder)
{
    auto b = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
    });

    std::vector<bytes32_t> salts;
    for (int i = 0; i < 3; ++i) {
        corpus::BlockSpec spec;
        Transaction tx{
            .max_fee_per_gas = 100,
            .gas_limit = 21000,
            .value = 1,
            .to = corpus::address_of(KEY_B),
            .type = TransactionType::eip1559,
            .max_priority_fee_per_gas = 1};
        tx.sc.chain_id = 1;
        spec.txs.push_back(tx);
        spec.keys.push_back(KEY_A);
        auto const e = b.add_block(std::move(spec));

        // extra_data is exactly the blinder, which is what makes the block
        // hash blinded -- and what the guest asserts before it will proceed.
        ASSERT_EQ(e.header.extra_data.size(), 32u);
        bytes32_t carried{};
        std::memcpy(carried.bytes, e.header.extra_data.data(), 32);
        EXPECT_EQ(carried, b.block_salt(e.header.number));
        salts.push_back(carried);
    }

    // Per block, not per chain.
    EXPECT_NE(salts[0], salts[1]);
    EXPECT_NE(salts[1], salts[2]);
    EXPECT_NE(salts[0], salts[2]);
}

// A different secret gives a different blinder at the same height, which is
// what makes the commitment to the secret worth checking.
TEST(CorpusBlinder, TheBlinderFollowsTheSecret)
{
    auto seeder = [](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
    };
    corpus::CorpusBuilder a{seeder, OPERATOR_SK, SALT_SECRET};
    bytes32_t other = SALT_SECRET;
    other.bytes[31] ^= 1u;
    corpus::CorpusBuilder c{seeder, OPERATOR_SK, other};

    EXPECT_NE(
        a.block_salt(corpus::GENESIS_NUMBER + 1),
        c.block_salt(corpus::GENESIS_NUMBER + 1));
}
#endif

// ---------------------------------------------------------------------------
// The fast genesis route, and the two things that make it trustworthy: it
// agrees with the slow one, and it agrees with itself at any chunk size.
// ---------------------------------------------------------------------------

namespace
{
    constexpr auto CONTRACT_ADDR =
        0x00000000000000000000000000000000000c0de9_address;
    constexpr auto SLOT_ONE =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto SLOT_TWO =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    constexpr auto VALUE_ONE =
        0x00000000000000000000000000000000000000000000000000000000000000aa_bytes32;
    constexpr auto VALUE_TWO =
        0x00000000000000000000000000000000000000000000000000000000000000bb_bytes32;

    /// PUSH1 0 PUSH1 0 SSTORE STOP, just to give the contract a code hash.
    byte_string const SOME_CODE =
        byte_string{0x60, 0x00, 0x60, 0x00, 0x55, 0x00};
}

TEST(GenesisBulk, TheFastRouteGivesTheSameRootAsTheSlowOne)
{
    // Whatever the two routes disagree on internally -- and they do disagree
    // on incarnation, which create_contract bumps and a hand-built delta does
    // not -- the STATE ROOT cannot see it: the merkle leaf is
    // rlp::encode_account(account, storage_root), four fields, and the
    // incarnation is not one of them. So this compares the only thing that
    // has to match.
    auto slow = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
        s.add_to_balance(corpus::address_of(KEY_B), 22_u256);
        s.set_nonce(corpus::address_of(KEY_B), 5);
        s.create_contract(CONTRACT_ADDR);
        s.set_code(CONTRACT_ADDR, SOME_CODE);
        s.add_to_balance(CONTRACT_ADDR, 7_u256);
        s.set_storage(CONTRACT_ADDR, SLOT_ONE, VALUE_ONE);
        s.set_storage(CONTRACT_ADDR, SLOT_TWO, VALUE_TWO);
    });

    auto const fast_seeder = [](corpus::GenesisSink &sink) {
        sink.account(
            corpus::address_of(KEY_A),
            Account{.balance = 1000000000000000000_u256});
        sink.account(
            corpus::address_of(KEY_B), Account{.balance = 22, .nonce = 5});
        sink.contract(CONTRACT_ADDR, Account{.balance = 7}, SOME_CODE);
        sink.storage(CONTRACT_ADDR, SLOT_ONE, VALUE_ONE);
        sink.storage(CONTRACT_ADDR, SLOT_TWO, VALUE_TWO);
    };
    corpus::CorpusBuilder fast{
        fast_seeder, 100'000, corpus::GAS_LIMIT, OPERATOR_SK, SALT_SECRET};

    EXPECT_EQ(fast.db().state_root(), slow.db().state_root());
}

TEST(GenesisBulk, ChunkingDoesNotChangeTheRoot)
{
    // 1000 accounts, once in a single commit and once in chunks that do not
    // divide it. Chunk boundaries land mid-account-run in the second, and an
    // account's storage has to stay with it, which is the property the sink's
    // flush-at-the-start-of-account rule exists for.
    auto const seeder = [](corpus::GenesisSink &sink) {
        for (uint64_t i = 0; i < 1000; ++i) {
            auto const key = corpus::derive_key(bytes32_t{}, 900'000 + i);
            Address a;
            std::memcpy(a.bytes, key.bytes + 12, sizeof(a.bytes));
            sink.account(a, Account{.balance = uint256_t{1000 + i}});
            sink.storage(a, SLOT_ONE, VALUE_ONE);
        }
    };
    corpus::CorpusBuilder one{
        seeder, 100'000, corpus::GAS_LIMIT, OPERATOR_SK, SALT_SECRET};
    corpus::CorpusBuilder many{
        seeder, 337, corpus::GAS_LIMIT, OPERATOR_SK, SALT_SECRET};

    EXPECT_EQ(one.db().state_root(), many.db().state_root());
}

// ---------------------------------------------------------------------------
// The node counter. witness_stats aborts if the nodes do not tile the blob, so
// merely running it on every block is most of the test; what is left is that
// the widths it attributes add back up.
// ---------------------------------------------------------------------------

TEST(WitnessStats, TheNodesTileEveryBlockOfEveryScenario)
{
    for (auto const &s : corpus::all_scenarios(bytes32_t{})) {
        auto b = make_builder(s.genesis);
        for (auto &spec : s.blocks(b)) {
            auto const e = b.add_block(std::move(spec));
            auto const st = corpus::witness_stats(e.witness);

            EXPECT_EQ(st.reconstructed_blob_bytes(), st.blob_bytes)
                << "scenario " << s.name << " block " << e.header.number;
            EXPECT_EQ(st.branch_bytes, st.branches * 65u);
            EXPECT_EQ(st.digest_bytes, st.digests * mpt::DIGEST_NODE_LEN);
            EXPECT_EQ(st.witness_bytes, e.witness.size());
            // A block that changed the state touched at least one account,
            // and reaching it needed at least one branch above it.
            EXPECT_GE(st.acct_leaves, 1u);
            EXPECT_GE(st.branches, 1u);
        }
    }
}

// ---------------------------------------------------------------------------
// The law the corpus exists to establish, frozen as a test.
//
// Cost tracks witness bytes, and a witness is mostly digests of siblings the
// block did not touch. A leaf touched twice in one block is free -- it is
// already there. So the access DISTRIBUTION can only reach the cost through
// the number of distinct leaves it produces, and at equal distinct count the
// three shapes should cost the same.
//
// Measured on a 200k-account state at distinct=300, four blocks: 24.32
// digests per leaf uniform, 24.07 zipf, 24.45 hot-set -- a 1.6% spread, next
// to a 1.8x swing across the distinct values themselves. The bound below is
// 8%, five times the observed spread, because this is a floor under the
// claim and not a re-measurement of it. If it ever fails, the reasoning above
// is wrong, and that is the finding.
// ---------------------------------------------------------------------------

TEST(WorkloadDispersion, TheShapeDoesNotChangeTheCostAtEqualDistinct)
{
    auto const run = [](corpus::Shape const shape) {
        corpus::WorkloadSpec spec{};
        spec.preset = corpus::Preset::Payouts;
        spec.shape = shape;
        spec.accounts = 20'000;
        spec.blocks = 2;
        spec.distinct = 200;
        corpus::Workload w{spec};
        corpus::CorpusBuilder b{
            w.seeder(),
            w.spec().chunk,
            w.spec().gas_limit(),
            OPERATOR_SK,
            SALT_SECRET};

        size_t leaves = 0;
        size_t digests = 0;
        for (uint64_t i = 0; i < w.block_count(); ++i) {
            auto const e = b.add_block(w.block(b, i));
            auto const st = corpus::witness_stats(e.witness);
            leaves += st.touched_leaves();
            digests += st.digests;
        }
        EXPECT_GT(leaves, 0u);
        return static_cast<double>(digests) / static_cast<double>(leaves);
    };

    double const uniform = run(corpus::Shape::Uniform);
    double const zipf = run(corpus::Shape::Zipf);
    double const hotset = run(corpus::Shape::HotSet);

    for (double const other : {zipf, hotset}) {
        EXPECT_LT(std::abs(other - uniform) / uniform, 0.08)
            << "uniform " << uniform << " vs " << other;
    }
}

// The other half of the same law: the distinct count is what moves, and it
// moves a lot. Sublinearly, because deeper paths share more of their prefix --
// which is why a benchmark has to sweep it rather than quote one number.
TEST(WorkloadDispersion, MoreDistinctAccountsCostMoreButSublinearly)
{
    auto const bytes_at = [](uint64_t const distinct) {
        corpus::WorkloadSpec spec{};
        spec.preset = corpus::Preset::Payouts;
        spec.shape = corpus::Shape::Uniform;
        spec.accounts = 20'000;
        spec.blocks = 1;
        spec.distinct = distinct;
        corpus::Workload w{spec};
        corpus::CorpusBuilder b{
            w.seeder(),
            w.spec().chunk,
            w.spec().gas_limit(),
            OPERATOR_SK,
            SALT_SECRET};
        // Block 0 deploys; block 1 is the first one that draws.
        b.add_block(w.block(b, 0));
        auto const e = b.add_block(w.block(b, 1));
        return corpus::witness_stats(e.witness);
    };

    auto const small = bytes_at(100);
    auto const large = bytes_at(400);

    EXPECT_GT(large.blob_bytes, small.blob_bytes);
    // Four times the accounts for less than four times the bytes: the extra
    // paths land under prefixes the first hundred already paid for.
    EXPECT_LT(large.blob_bytes, 4 * small.blob_bytes);
    EXPECT_LT(
        static_cast<double>(large.blob_bytes) /
            static_cast<double>(large.touched_leaves()),
        static_cast<double>(small.blob_bytes) /
            static_cast<double>(small.touched_leaves()));
}
