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

#include <zkvm/test/corpus/contracts/namespace_spoke_bytecode.hpp>
#include <zkvm/test/corpus/corpus_builder.hpp>
#include <zkvm/test/corpus/genesis_bulk.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
#include <zkvm/test/corpus/spoke_code.hpp>
#include <zkvm/test/corpus/token_contracts.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>
#include <zkvm/test/corpus/witness_stats.hpp>
#include <zkvm/test/corpus/workload.hpp>

#include <category/core/hex.hpp>
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

#include <algorithm>
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
        // Eight fields here and six otherwise, and each shape rejects the
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
    // Every ancestor, so there is a run to chain whatever the build's default.
    b.set_ancestors(corpus::Ancestors::All);

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
// How far back field [3] reaches. Ancestors::Reached carries the run from the
// oldest block whose hash the block read to the parent -- the parent alone for
// a block that reads none, exactly three headers for one that reads three
// blocks back -- and Ancestors::All every header the buffer holds. That the
// guest accepts the shorter run, and refuses one shorter than the block reads,
// is test_witness_rejection's to show.
// ---------------------------------------------------------------------------

namespace
{
    /// The block numbers field [3] carries, oldest first.
    std::vector<uint64_t> ancestor_numbers(byte_string const &witness)
    {
#ifdef MONAD_ZKVM_L2
        auto parsed = parse_execution_witness_l2(witness);
        MONAD_ASSERT(parsed.has_value());
        byte_string_view rest = parsed.value().base.encoded_headers;
#else
        auto parsed = parse_execution_witness(witness);
        MONAD_ASSERT(parsed.has_value());
        byte_string_view rest = parsed.value().encoded_headers;
#endif
        std::vector<uint64_t> numbers;
        while (!rest.empty()) {
            auto item = rlp::parse_string_metadata(rest);
            MONAD_ASSERT(item.has_value());
            byte_string_view hv = item.value();
            auto const h = rlp::decode_block_header(hv);
            MONAD_ASSERT(h.has_value());
            numbers.push_back(h.value().number);
        }
        return numbers;
    }

    constexpr auto HASH_READER =
        0x000000000000000000000000000000000000b10c_address;
    /// SSTORE(0, BLOCKHASH(NUMBER - 3)): one hash, read three blocks back.
    byte_string const READS_A_HASH =
        byte_string{0x60, 0x03, 0x43, 0x03, 0x40, 0x60, 0x00, 0x55, 0x00};

    corpus::BlockSpec one_call(Address const &to, uint64_t const gas)
    {
        corpus::BlockSpec spec;
        Transaction tx{
            .max_fee_per_gas = 0,
            .gas_limit = gas,
            .value = 1,
            .to = to,
            .type = TransactionType::eip1559};
        tx.sc.chain_id = 1;
        spec.txs.push_back(tx);
        spec.keys.push_back(KEY_A);
        return spec;
    }
}

TEST(CorpusBuilder, AncestorsReachBackToTheOldestHashTheBlockReads)
{
    auto b = make_builder([](State &s) {
        s.add_to_balance(corpus::address_of(KEY_A), 1000000000000000000_u256);
        s.create_contract(HASH_READER);
        s.set_code(HASH_READER, READS_A_HASH);
    });
    b.set_ancestors(corpus::Ancestors::Reached);

    for (int i = 0; i < 4; ++i) {
        auto const e = b.add_block(one_call(corpus::address_of(KEY_B), 21000));
        EXPECT_EQ(
            ancestor_numbers(e.witness),
            std::vector<uint64_t>{e.header.number - 1});
    }

    auto const read = b.add_block(one_call(HASH_READER, 100000));
    ASSERT_EQ(read.receipts.at(0).status, 1u);
    uint64_t const n = read.header.number;
    EXPECT_EQ(
        ancestor_numbers(read.witness),
        (std::vector<uint64_t>{n - 3, n - 2, n - 1}));

    b.set_ancestors(corpus::Ancestors::All);
    auto const all = b.add_block(one_call(corpus::address_of(KEY_B), 21000));
    std::vector<uint64_t> every;
    for (uint64_t k = corpus::GENESIS_NUMBER; k < all.header.number; ++k) {
        every.push_back(k);
    }
    EXPECT_EQ(ancestor_numbers(all.witness), every);
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

// ---------------------------------------------------------------------------
// An L2 genesis seeds the spoke rather than deploying it, from its runtime code
// with the two immutables written in where solc says the constructor writes
// them. That is only the spoke if it is byte for byte what a deployment
// leaves, so deploy one and compare.
// ---------------------------------------------------------------------------

TEST(CorpusScenarios, TheGenesisSpokeIsTheDeployedSpoke)
{
    auto const deployer = corpus::address_of(KEY_A);
    Address const op = corpus::address_of(KEY_B);
    auto b = make_builder([&](State &s) {
        s.add_to_balance(deployer, 1000000000000000000_u256);
    });
    Address const at = b.next_contract_address(deployer);

    auto init = from_hex(corpus::NAMESPACE_SPOKE_CREATION_HEX);
    ASSERT_TRUE(init.has_value());
    byte_string data = std::move(init).value();
    for (auto const &w :
         {corpus::tokens::word(uint256_t{7}), corpus::tokens::word(op)}) {
        data.append(w.bytes, sizeof(w.bytes));
    }
    Transaction tx{
        .max_fee_per_gas = 0,
        .gas_limit = 2'000'000,
        .type = TransactionType::eip1559,
        .data = std::move(data)};
    tx.sc.chain_id = 1;
    corpus::BlockSpec spec;
    spec.txs.push_back(tx);
    spec.keys.push_back(KEY_A);
    auto const e = b.add_block(std::move(spec));
    ASSERT_EQ(e.receipts.size(), 1u);
    ASSERT_EQ(e.receipts[0].status, 1u);

    auto const acct = b.db().read_account(at);
    ASSERT_TRUE(acct.has_value());
    auto const code = b.db().read_code(acct->code_hash);
    ASSERT_TRUE(code);
    EXPECT_EQ(
        byte_string(code->code(), code->size()),
        corpus::namespace_spoke_code(7, op));
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
        spec.warmup = 0;
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
        spec.blocks = 2;
        spec.warmup = 0;
        spec.distinct = distinct;
        corpus::Workload w{spec};
        corpus::CorpusBuilder b{
            w.seeder(),
            w.spec().chunk,
            w.spec().gas_limit(),
            OPERATOR_SK,
            SALT_SECRET};
        // Block 1 is measured on every build: outside an L2 one block 0
        // deploys the spoke, inside one the genesis already holds it and block
        // 0 is a first draw.
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

// ---------------------------------------------------------------------------
// The token presets. A reverted transaction still executes, still makes a
// valid block and still round-trips every root, so the roots say nothing about
// whether the workload did what it says: the receipts do. Every transaction
// of both presets has to succeed, and the logs have to add up to the flows.
// ---------------------------------------------------------------------------

namespace
{
    constexpr auto TRANSFER_TOPIC =
        abi_encode_event_signature("Transfer(address,address,uint256)");

    size_t transfer_logs(Receipt const &r)
    {
        size_t n = 0;
        for (auto const &log : r.logs) {
            n += !log.topics.empty() && log.topics[0] == TRANSFER_TOPIC;
        }
        return n;
    }
}

TEST(WorkloadTokens, EveryWholesaleCbdcTransactionSucceeds)
{
    for (uint64_t const currencies : {2u, 5u}) {
        SCOPED_TRACE(std::to_string(currencies) + " currencies");
        corpus::WorkloadSpec spec{};
        spec.preset = corpus::Preset::WholesaleCbdc;
        spec.accounts = 60;
        spec.blocks = 3;
        spec.warmup = 0;
        spec.distinct = 20;
        spec.currencies = currencies;
        // The seed the compiled spoke address was derived from, so the anchor
        // is harvested from the spoke this run deploys.
        spec.seed.bytes[31] = 1;
        corpus::Workload w{spec};
        corpus::CorpusBuilder b{
            w.seeder(),
            w.spec().chunk,
            w.spec().gas_limit(),
            OPERATOR_SK,
            SALT_SECRET};

        // distinct=20 is five payments a block: proposed in one, settled in
        // the next, so blocks 2 and 3 each settle five -- two token
        // transfers apiece, one per leg and each in its own currency, in one
        // transaction. With the redemptions, every currency moves.
        size_t settlements = 0;
        std::vector<Address> moved;
        for (uint64_t i = 0; i < w.block_count(); ++i) {
            auto const e = b.add_block(w.block(b, i));
            SCOPED_TRACE("block " + std::to_string(i));
            EXPECT_EQ(guest_view(e.witness).state_root(), e.pre_root);
            for (auto const &r : e.receipts) {
                EXPECT_EQ(r.status, 1u);
                settlements += transfer_logs(r) == 2;
                for (auto const &log : r.logs) {
                    if (!log.topics.empty() &&
                        log.topics[0] == TRANSFER_TOPIC &&
                        std::find(moved.begin(), moved.end(), log.address) ==
                            moved.end()) {
                        moved.push_back(log.address);
                    }
                }
            }
#ifdef MONAD_ZKVM_L2
            // The genesis holds the spoke and every block redeems reserves
            // through it, so every block carries an anchor.
            EXPECT_NE(e.namespace_anchor, bytes32_t{});
#endif
        }
        EXPECT_EQ(settlements, 10u);
        EXPECT_EQ(moved.size(), currencies);
    }
}

TEST(WorkloadTokens, EveryWorkerPayoutsTransactionSucceeds)
{
    corpus::WorkloadSpec spec{};
    spec.preset = corpus::Preset::WorkerPayouts;
    spec.accounts = 5'000;
    spec.blocks = 2;
    spec.warmup = 0;
    spec.distinct = 100;
    spec.seed.bytes[31] = 1;
    corpus::Workload w{spec};
    corpus::CorpusBuilder b{
        w.seeder(),
        w.spec().chunk,
        w.spec().gas_limit(),
        OPERATOR_SK,
        SALT_SECRET};

    b.add_block(w.block(b, 0));
    for (uint64_t i = 1; i < w.block_count(); ++i) {
        auto const e = b.add_block(w.block(b, i));
        SCOPED_TRACE("block " + std::to_string(i));
        EXPECT_EQ(guest_view(e.witness).state_root(), e.pre_root);
        size_t transfers = 0;
        for (auto const &r : e.receipts) {
            EXPECT_EQ(r.status, 1u);
            transfers += transfer_logs(r);
        }
        // One transfer per contractor touched -- a salary, a deposit or
        // withdrawal, or an exit -- and one per payroll batch funded: 100
        // contractors, 80 of them paid in two batches of at most forty.
        EXPECT_EQ(transfers, 102u);
        // The contractors are in the token's storage, not the account trie.
        EXPECT_GE(corpus::witness_stats(e.witness).storage_leaves, 100u);
    }
}

namespace
{
    constexpr auto KEY_C =
        0x0000000000000000000000000000000000000000000000000000000000000c33_bytes32;

    Transaction contract_call(Address const &to, byte_string data)
    {
        Transaction tx{
            .max_fee_per_gas = 0,
            .gas_limit = 300'000,
            .to = to,
            .type = TransactionType::eip1559,
            .data = std::move(data)};
        tx.sc.chain_id = 1;
        return tx;
    }

    Address fixed_address(unsigned char const tag)
    {
        Address a{};
        a.bytes[19] = tag;
        a.bytes[0] = 0xc0;
        return a;
    }

    /// A token balance slot as the contract stores it, eligibility bit
    /// included.
    bytes32_t held(uint256_t const &balance)
    {
        return corpus::tokens::word(balance | corpus::tokens::ELIGIBLE);
    }
}

// Eligibility is the token's, as the design asks: a balance moves only between
// holders the token has admitted, whichever end is missing the bit and
// whatever the balance says.
TEST(WrappedToken, OnlyAdmittedHoldersMoveBalances)
{
    using namespace corpus::tokens;
    Address const token = fixed_address(1);
    Address const admitted = fixed_address(2);
    Address const barred = fixed_address(3);
    auto const a = corpus::address_of(KEY_A);
    auto const b = corpus::address_of(KEY_B);

    corpus::CorpusBuilder builder{
        [&](corpus::GenesisSink &sink) {
            sink.account(a, Account{.balance = 1'000'000});
            sink.account(b, Account{.balance = 1'000'000});
            sink.contract(token, Account{.nonce = 1}, wrapped_token_code());
            sink.storage(token, balance_slot(a), held(1000));
            sink.storage(token, balance_slot(admitted), held(0));
            // A balance and no bit: never admitted, or since removed.
            sink.storage(token, balance_slot(b), word(uint256_t{1000}));
            sink.storage(
                token,
                word(uint256_t{TOTAL_SUPPLY_SLOT}),
                word(uint256_t{2000}));
        },
        1000,
        corpus::GAS_LIMIT,
        OPERATOR_SK,
        SALT_SECRET};

    corpus::BlockSpec spec;
    spec.txs.push_back(contract_call(token, transfer(barred, 10)));
    spec.keys.push_back(KEY_A);
    spec.txs.push_back(contract_call(token, transfer(admitted, 10)));
    spec.keys.push_back(KEY_B);
    spec.txs.push_back(contract_call(token, transfer(admitted, 10)));
    spec.keys.push_back(KEY_A);
    auto const e = builder.add_block(std::move(spec));

    ASSERT_EQ(e.receipts.size(), 3u);
    EXPECT_EQ(e.receipts[0].status, 0u) << "to a holder never admitted";
    EXPECT_EQ(e.receipts[1].status, 0u) << "from a holder never admitted";
    EXPECT_EQ(e.receipts[2].status, 1u);
    auto &db = builder.db();
    EXPECT_EQ(
        db.read_storage(token, Incarnation{0, 0}, balance_slot(a)), held(990));
    EXPECT_EQ(
        db.read_storage(token, Incarnation{0, 0}, balance_slot(admitted)),
        held(10));
    EXPECT_EQ(
        db.read_storage(token, Incarnation{0, 0}, balance_slot(b)),
        word(uint256_t{1000}));
}

// "The two interbank legs are conditioned on one another and settle together
// or not at all." The intermediary can pay the second leg of one payment and
// not of the other: the one it can pay moves both legs, and the one it cannot
// moves neither -- and stays pending, for the debtor to cancel or the
// intermediary to settle once funded.
TEST(PvpSettlement, BothLegsOrNeither)
{
    using namespace corpus::tokens;
    Address const t0 = fixed_address(1);
    Address const t1 = fixed_address(2);
    Address const pvp = fixed_address(3);
    auto const debtor = corpus::address_of(KEY_A);
    auto const intermediary = corpus::address_of(KEY_B);
    auto const creditor = corpus::address_of(KEY_C);
    uint256_t const max = ~uint256_t{0};

    corpus::CorpusBuilder builder{
        [&](corpus::GenesisSink &sink) {
            for (auto const &who : {debtor, intermediary, creditor}) {
                sink.account(who, Account{.balance = 1'000'000});
            }
            sink.contract(t0, Account{.nonce = 1}, wrapped_token_code());
            sink.storage(t0, balance_slot(debtor), held(1000));
            sink.storage(t0, balance_slot(intermediary), held(0));
            sink.storage(t0, allowance_slot(debtor, pvp), word(max));
            sink.storage(
                t0, word(uint256_t{TOTAL_SUPPLY_SLOT}), word(uint256_t{1000}));
            sink.contract(t1, Account{.nonce = 1}, wrapped_token_code());
            sink.storage(t1, balance_slot(intermediary), held(50));
            sink.storage(t1, balance_slot(creditor), held(0));
            sink.storage(t1, allowance_slot(intermediary, pvp), word(max));
            sink.storage(
                t1, word(uint256_t{TOTAL_SUPPLY_SLOT}), word(uint256_t{50}));
            sink.contract(pvp, Account{.nonce = 1}, pvp_settlement_code());
        },
        1000,
        corpus::GAS_LIMIT,
        OPERATOR_SK,
        SALT_SECRET};

    Payment const affordable{
        .ref = 1,
        .token_a = t0,
        .debtor = debtor,
        .intermediary = intermediary,
        .amount_a = 48,
        .token_b = t1,
        .creditor = creditor,
        .amount_b = 40};
    Payment unaffordable = affordable;
    unaffordable.ref = 2;
    unaffordable.amount_a = 72;
    unaffordable.amount_b = 60;

    corpus::BlockSpec spec;
    spec.txs.push_back(contract_call(pvp, propose(unaffordable)));
    spec.keys.push_back(KEY_A);
    spec.txs.push_back(contract_call(pvp, propose(affordable)));
    spec.keys.push_back(KEY_A);
    // Only the intermediary may settle.
    spec.txs.push_back(contract_call(pvp, settle(affordable)));
    spec.keys.push_back(KEY_C);
    spec.txs.push_back(contract_call(pvp, settle(unaffordable)));
    spec.keys.push_back(KEY_B);
    spec.txs.push_back(contract_call(pvp, settle(affordable)));
    spec.keys.push_back(KEY_B);
    auto const e = builder.add_block(std::move(spec));

    ASSERT_EQ(e.receipts.size(), 5u);
    EXPECT_EQ(e.receipts[0].status, 1u);
    EXPECT_EQ(e.receipts[1].status, 1u);
    EXPECT_EQ(e.receipts[2].status, 0u) << "settled by the creditor";
    EXPECT_EQ(e.receipts[3].status, 0u) << "second leg unaffordable";
    EXPECT_EQ(e.receipts[4].status, 1u);

    auto &db = builder.db();
    auto const slot = [&](Address const &c, bytes32_t const &k) {
        return db.read_storage(c, Incarnation{0, 0}, k);
    };
    // The affordable payment moved both legs, and nothing else moved.
    EXPECT_EQ(slot(t0, balance_slot(debtor)), held(952));
    EXPECT_EQ(slot(t0, balance_slot(intermediary)), held(48));
    EXPECT_EQ(slot(t1, balance_slot(intermediary)), held(10));
    EXPECT_EQ(slot(t1, balance_slot(creditor)), held(40));
    EXPECT_EQ(slot(pvp, pvp_pending_slot(payment_id(affordable))), bytes32_t{});
    EXPECT_EQ(
        slot(pvp, pvp_pending_slot(payment_id(unaffordable))),
        word(uint256_t{1}));
}
