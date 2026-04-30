// Copyright (C) 2025 Category Labs, Inc.
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

#include <blockchain_test.hpp>
#include <category/core/log.hpp>
#include <event.hpp>
#include <revision_map.hpp>
#include <tracking_block_hash_buffer.hpp>

#include <test/utils/from_json.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/event/event_iterator.h>
#include <category/core/event/event_ring.h>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/exec_iter_help.h>
#include <category/execution/ethereum/event/record_block_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <gtest/gtest.h>

#include <memory>
#include <test_resource_data.h>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <set>
#include <span>
#include <string>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <Traits traits>
struct TraitsMainnet : MonadChain
{
    TraitsMainnet() = default;

    virtual uint256_t get_chain_id() const override
    {
        if constexpr (is_evm_trait_v<traits>) {
            return EthereumMainnet{}.get_chain_id();
        }
        else {
            return MonadMainnet{}.get_chain_id();
        }
    }

    virtual evmc_revision get_revision(
        uint64_t /* block_number */, uint64_t /* timestamp */) const override
    {
        return traits::evm_rev();
    }

    virtual monad_revision
    get_monad_revision(uint64_t /* timestamp */) const override
    {
        if constexpr (is_monad_trait_v<traits>) {
            return traits::monad_rev();
        }
        MONAD_ASSERT(false);
    }

    virtual GenesisState get_genesis_state() const override
    {
        if constexpr (is_evm_trait_v<traits>) {
            return EthereumMainnet{}.get_genesis_state();
        }
        else {
            return MonadMainnet{}.get_genesis_state();
        }
    }
};

static fiber::PriorityPool *pool_ = nullptr;

static ankerl::unordered_dense::segmented_set<Address> const
    empty_senders_and_authorities{};

void validate_post_state(nlohmann::json const &json, nlohmann::json const &db)
{
    EXPECT_EQ(db.size(), json.size());

    for (auto const &[addr, j_account] : json.items()) {
        nlohmann::json const addr_json = addr;
        auto const addr_bytes = addr_json.get<Address>();
        auto const hashed_account = to_bytes(keccak256(addr_bytes.bytes));
        auto const db_addr_key = fmt::format("{}", hashed_account);

        EXPECT_TRUE(db.contains(db_addr_key))
            << fmt::format("{} ({})", db_addr_key, addr_bytes);
        if (!db.contains(db_addr_key)) {
            continue;
        }
        auto const &db_account = db.at(db_addr_key);

        auto const expected_balance =
            fmt::format("{}", j_account.at("balance").get<uint256_t>());
        auto const expected_nonce = fmt::format(
            "0x{:x}", integer_from_json<uint64_t>(j_account.at("nonce")));
        auto const code = j_account.contains("code")
                              ? j_account.at("code").get<monad::byte_string>()
                              : monad::byte_string{};
        auto const expected_code = fmt::format(
            "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));

        EXPECT_EQ(db_account.at("balance").get<std::string>(), expected_balance)
            << fmt::format("{} ({})", db_addr_key, addr_bytes);
        EXPECT_EQ(db_account.at("nonce").get<std::string>(), expected_nonce)
            << fmt::format("{} ({})", db_addr_key, addr_bytes);
        EXPECT_EQ(db_account.at("code").get<std::string>(), expected_code)
            << fmt::format("{} ({})", db_addr_key, addr_bytes);

        auto const &db_storage = db_account.at("storage");
        std::set<std::string> db_storage_keys_in_j;

        EXPECT_EQ(db_storage.size(), j_account.at("storage").size())
            << fmt::format("{} ({})", db_addr_key, addr_bytes);
        for (auto const &[key, j_value] : j_account.at("storage").items()) {
            nlohmann::json const key_json = key;
            auto const key_bytes = key_json.get<bytes32_t>();
            auto const db_storage_key =
                fmt::format("{}", to_bytes(keccak256(key_bytes.bytes)));
            EXPECT_TRUE(db_storage.contains(db_storage_key))
                << fmt::format("{} ({})", db_storage_key, key_bytes);
            if (db_storage.contains(db_storage_key)) {
                db_storage_keys_in_j.emplace(db_storage_key);
                auto const expected_value =
                    fmt::format("{}", j_value.get<bytes32_t>());
                EXPECT_EQ(
                    db_storage.at(db_storage_key).at("value"), expected_value)
                    << fmt::format("{} ({})", db_storage_key, key_bytes);
            }
        }
        for (auto const &[key, db_value] : db_account.at("storage").items()) {
            auto const db_storage_value_bytes =
                db_value.at("value").get<bytes32_t>();
            // The previous loop has already checked for all key-value pairs of
            // j_account whether there exists a corresponding pair in the db.
            // So, it remains to check whether every db key has a corresponding
            // entry in j_account.
            EXPECT_TRUE(db_storage_keys_in_j.contains(key)) << fmt::format(
                "Unexpected kv in db ({} => {})", key, db_storage_value_bytes);
        }
    }
}

template <Traits traits>
Result<BlockExecOutput> execute(
    Block &block, Db &db, vm::VM &vm, BlockHashBuffer const &block_hash_buffer,
    std::map<uint64_t, ankerl::unordered_dense::segmented_set<Address>>
        &senders_and_authorities_map,
    bool enable_tracing, std::vector<Receipt> &receipts,
    std::vector<std::vector<CallFrame>> &call_frames,
    std::function<void(StateDeltas const &)> const &on_pre_commit = {})
{
    using namespace monad::test;

    TraitsMainnet<traits> const chain{};
    BOOST_OUTCOME_TRY(static_validate_block<traits>(chain, block));

    BlockState block_state(db, vm);
    BlockMetrics metrics;
    auto const recovered_senders = recover_senders(block.transactions, *pool_);
    auto const recovered_authorities =
        recover_authorities(block.transactions, *pool_);
    std::vector<Address> senders(block.transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        if (recovered_senders[i].has_value()) {
            senders[i] = recovered_senders[i].value();
        }
        else {
            return TransactionError::MissingSender;
        }
    }

    std::vector<std::unique_ptr<CallTracerBase>> call_tracers{
        block.transactions.size()};
    call_frames.resize(block.transactions.size());
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers{
        block.transactions.size()};
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        call_tracers[i] =
            enable_tracing
                ? std::unique_ptr<CallTracerBase>{std::make_unique<CallTracer>(
                      block.transactions[i], call_frames[i])}
                : std::unique_ptr<CallTracerBase>{
                      std::make_unique<NoopCallTracer>()};
        state_tracers[i] = std::unique_ptr<trace::StateTracer>{
            std::make_unique<trace::StateTracer>(std::monostate{})};
    }

    senders_and_authorities_map[block.header.number] =
        combine_senders_and_authorities(senders, recovered_authorities);
    auto &senders_and_authorities =
        senders_and_authorities_map[block.header.number];

    ChainContext<traits> chain_context = [&] {
        if constexpr (is_monad_trait_v<traits>) {
            return ChainContext<traits>{
                .grandparent_senders_and_authorities =
                    (block.header.number > 1
                         ? senders_and_authorities_map[block.header.number - 2]
                         : empty_senders_and_authorities),
                .parent_senders_and_authorities =
                    senders_and_authorities_map[block.header.number - 1],
                .senders_and_authorities = senders_and_authorities,
                .senders = senders,
                .authorities = recovered_authorities};
        }
        else {
            return ChainContext<traits>{};
        }
    }();

    BOOST_OUTCOME_TRY(
        receipts,
        execute_block<traits>(
            chain,
            block,
            senders,
            recovered_authorities,
            block_state,
            block_hash_buffer,
            pool_->fiber_group(),
            metrics,
            call_tracers,
            state_tracers,
            chain_context));

    block_state.log_debug();
    auto [state, code] = std::move(block_state).release();

    if (on_pre_commit) {
        on_pre_commit(*state);
    }

    CommitBuilder builder(block.header.number);
    builder.add_state_deltas(*state)
        .add_code(code)
        .add_receipts(receipts)
        .add_transactions(block.transactions, senders)
        .add_call_frames(
            std::vector<std::vector<CallFrame>>(block.transactions.size()))
        .add_ommers(block.ommers);
    if (block.withdrawals.has_value()) {
        builder.add_withdrawals(block.withdrawals.value());
    }
    db.commit(
        bytes32_t{block.header.number},
        builder,
        block.header,
        *state,
        [&](BlockHeader &h) {
            if constexpr (traits::evm_rev() <= EVMC_BYZANTIUM) {
                // TrieDb receipts root is not valid pre-Byzantium; use the
                // block's original receipts root.
                h.receipts_root = block.header.receipts_root;
            }
            else {
                h.receipts_root = db.receipts_root();
            }
            h.state_root = db.state_root();
            h.withdrawals_root = db.withdrawals_root();
            h.transactions_root = db.transactions_root();
            h.gas_used = receipts.empty() ? 0 : receipts.back().gas_used;
            h.logs_bloom = compute_bloom(receipts);
            h.ommers_hash = compute_ommers_hash(block.ommers);
        });

    db.finalize(block.header.number, bytes32_t{block.header.number});

    BlockExecOutput exec_output;
    exec_output.eth_header = db.read_eth_header();
    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));

    BOOST_OUTCOME_TRY(
        validate_output_header(block.header, exec_output.eth_header));

    return exec_output;
}

template <Traits traits>
Result<std::vector<Receipt>> execute_and_record(
    Block &block, monad::TrieDb &db, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    std::map<uint64_t, ankerl::unordered_dense::segmented_set<Address>>
        &senders_and_authorities_map,
    bool enable_tracing)
{
    record_block_start(
        bytes32_t{block.header.number},
        /*chain_id*/ 1,
        block.header,
        block.header.parent_hash,
        block.header.number,
        0,
        block.header.timestamp * 1'000'000'000UL,
        size(block.transactions),
        std::nullopt,
        std::nullopt);

    std::vector<Receipt> receipts;
    std::vector<std::vector<CallFrame>> call_frames;

    auto result = record_block_result(execute<traits>(
        block,
        db,
        vm,
        block_hash_buffer,
        senders_and_authorities_map,
        enable_tracing,
        receipts,
        call_frames));
    if (result.has_error()) {
        // TODO(ken): why is std::move required here?
        return std::move(result.error());
    }
    else {
        return receipts;
    }
}

template <Traits traits>
void process_test(
    std::string const &name, nlohmann::json const &j_contents,
    bool enable_tracing, bool witness_roundtrip)
{
    using namespace test;

    auto const json_state = load_blockchain_json_state<traits>(j_contents);
    auto const test_state = json_state.make_test_state();
    // Owned here so the tracker outlives ptdb_gen (which holds it by ref)
    // and so the test body can reset it between blocks.
    AccessTracker gen_tracker;
    std::optional<PartialTrieDb<AccessTracker>> ptdb_gen{};
    std::vector<byte_string> ancestor_headers_gen;
    std::map<uint64_t, ankerl::unordered_dense::segmented_set<Address>>
        senders_and_authorities_map_gen{};
    vm::VM vm;
    // Shared across round-trip re-executions. rebuilt is fresh per block
    // but its codes overlap across blocks (and pre-state codes repeat
    // every block), so keeping a warm varcode cache avoids recompiling
    // the same bytecode for every block.
    vm::VM vm_reexec;
    mpt::Db &db = test_state->db;
    monad::TrieDb &tdb = test_state->trie_db;

    if (witness_roundtrip) {
        ptdb_gen.emplace(gen_tracker);
        BlockState bs_gen{*ptdb_gen, vm};
        State state_gen{bs_gen, Incarnation{0, 0}};
        j_contents.at("pre").get_to(state_gen);
        bs_gen.merge(state_gen);
        auto [rs_gen, rc_gen] = std::move(bs_gen).release();
        commit_simple(
            *ptdb_gen,
            *rs_gen,
            rc_gen,
            NULL_HASH_BLAKE3,
            json_state.header,
            {},
            {},
            {},
            {},
            {},
            json_state.withdrawals);
        ASSERT_EQ(ptdb_gen->state_root(), tdb.state_root());
        // Use tdb's post-commit header as the genesis ancestor: it has
        // the full set of populated fields (state_root, withdrawals_root,
        // receipts_root, ...). ptdb_gen's post-commit header has nullopt
        // withdrawals_root because PartialTrieDb doesn't track it.
        ancestor_headers_gen.push_back(
            rlp::encode_block_header(tdb.read_eth_header()));
        senders_and_authorities_map_gen[0] =
            ankerl::unordered_dense::segmented_set<Address>{};
    }
    auto db_post_state = tdb.to_json();

    BlockHashBufferFinalized block_hash_buffer;

    std::map<uint64_t, ankerl::unordered_dense::segmented_set<Address>>
        senders_and_authorities_map{};
    // genesis block has no senders or authorities
    senders_and_authorities_map[0] =
        ankerl::unordered_dense::segmented_set<Address>{};

    for (auto const &j_block : j_contents.at("blocks")) {

        auto const block_rlp = j_block.at("rlp").get<byte_string>();
        byte_string_view block_rlp_view{block_rlp};
        auto block = rlp::decode_block(block_rlp_view);
        if (block.has_error() || !block_rlp_view.empty()) {
            EXPECT_TRUE(j_block.contains("expectException")) << name;
            continue;
        }

        if (block.value().header.number == 0) {
            EXPECT_TRUE(j_block.contains("expectException")) << name;
            continue;
        }
        if (j_block.contains("blocknumber") &&
            block.value().header.number !=
                std::stoull(j_block.at("blocknumber").get<std::string>())) {
            EXPECT_TRUE(j_block.contains("expectException")) << name;
            continue;
        }

        block_hash_buffer.set(
            block.value().header.number - 1, block.value().header.parent_hash);

        uint64_t const curr_block_number = block.value().header.number;
        auto const result = execute_and_record<traits>(
            block.value(),
            tdb,
            vm,
            block_hash_buffer,
            senders_and_authorities_map,
            enable_tracing);

        ExecutionEvents exec_events{};
        bool check_exec_events = false; // Won't do gtest checks if disabled

        if (auto const *const exec_recorder = g_exec_event_recorder.get()) {
            // Event recording is enabled; rewind the iterator to the
            // BLOCK_START event for the given block number
            monad_event_iterator iter;
            monad_event_ring const *const exec_ring =
                exec_recorder->get_event_ring();
            ASSERT_EQ(monad_event_ring_init_iterator(exec_ring, &iter), 0);
            ASSERT_TRUE(monad_exec_iter_block_number_prev(
                &iter,
                exec_ring,
                curr_block_number,
                MONAD_EXEC_BLOCK_START,
                nullptr));
            find_execution_events(
                exec_recorder->get_event_ring(), &iter, &exec_events);
            check_exec_events = true;
        }

        if (!result.has_error()) {
            db_post_state = tdb.to_json();
            EXPECT_FALSE(j_block.contains("expectException")) << name;
            EXPECT_EQ(tdb.get_block_number(), curr_block_number) << name;
            auto const root = tdb.get_root();
            EXPECT_EQ(tdb.state_root(), block.value().header.state_root)
                << name;
            EXPECT_EQ(
                tdb.transactions_root(), block.value().header.transactions_root)
                << name;
            EXPECT_EQ(
                tdb.withdrawals_root(), block.value().header.withdrawals_root)
                << name;
            auto const ommers_res = db.find(
                root,
                mpt::concat(FINALIZED_NIBBLE, OMMER_NIBBLE),
                curr_block_number);
            ASSERT_TRUE(ommers_res.has_value()) << name;
            auto const encoded_ommers = ommers_res.value().node->value();
            auto const tdb_ommers_hash = to_bytes(keccak256(encoded_ommers));
            EXPECT_EQ(tdb_ommers_hash, block.value().header.ommers_hash)
                << name;
            if constexpr (traits::evm_rev() >= EVMC_BYZANTIUM) {
                EXPECT_EQ(
                    tdb.receipts_root(), block.value().header.receipts_root)
                    << name;
            }
            EXPECT_EQ(result.value().size(), block.value().transactions.size())
                << name;

            if (check_exec_events) {
                EXPECT_FALSE(exec_events.block_reject_code) << name;
                EXPECT_EQ(
                    bytes32_t(exec_events.block_end->exec_output.state_root),
                    tdb.state_root())
                    << name;
                EXPECT_EQ(
                    bytes32_t(exec_events.block_start->eth_block_input
                                  .transactions_root),
                    tdb.transactions_root())
                    << name;
                if (tdb.withdrawals_root()) {
                    EXPECT_EQ(
                        bytes32_t(exec_events.block_start->eth_block_input
                                      .withdrawals_root),
                        *tdb.withdrawals_root())
                        << name;
                }
                else {
                    EXPECT_EQ(
                        bytes32_t(exec_events.block_start->eth_block_input
                                      .withdrawals_root),
                        bytes32_t{})
                        << name;
                }
                EXPECT_EQ(
                    bytes32_t(
                        exec_events.block_start->eth_block_input.ommers_hash),
                    tdb_ommers_hash)
                    << name;
                if constexpr (traits::evm_rev() >= EVMC_BYZANTIUM) {
                    EXPECT_EQ(
                        bytes32_t(
                            exec_events.block_end->exec_output.receipts_root),
                        tdb.receipts_root())
                        << name;
                }
                EXPECT_EQ(
                    exec_events.block_start->eth_block_input.txn_count,
                    result.value().size())
                    << name;
            }

            { // verify block header is stored correctly
                BlockHeader const header = tdb.read_eth_header();
                EXPECT_EQ(header, block.value().header) << name;
            }
            { // look up block hash
                auto const block_hash =
                    keccak256(rlp::encode_block_header(block.value().header));
                auto res = db.find(
                    root,
                    mpt::concat(
                        FINALIZED_NIBBLE,
                        BLOCK_HASH_NIBBLE,
                        mpt::NibblesView{block_hash}),
                    curr_block_number);
                EXPECT_TRUE(res.has_value()) << name;
                auto encoded_number = res.value().node->value();
                auto const decoded_number =
                    rlp::decode_unsigned<uint64_t>(encoded_number);
                EXPECT_TRUE(decoded_number.has_value()) << name;
                EXPECT_EQ(decoded_number.value(), curr_block_number) << name;
            }
            // verify tx hash
            for (unsigned i = 0; i < block.value().transactions.size(); ++i) {
                auto const &tx = block.value().transactions[i];
                auto const hash = keccak256(rlp::encode_transaction(tx));
                auto find_res = db.find(
                    root,
                    mpt::concat(
                        FINALIZED_NIBBLE,
                        TX_HASH_NIBBLE,
                        mpt::NibblesView{hash}),
                    curr_block_number);
                EXPECT_TRUE(find_res.has_value()) << name;
                auto const tx_hash = find_res.value().node->value();
                EXPECT_EQ(
                    tx_hash,
                    rlp::encode_list2(
                        rlp::encode_unsigned(curr_block_number),
                        rlp::encode_unsigned(i)))
                    << name;

                if (check_exec_events) {
                    ASSERT_LT(i, size(exec_events.txn_inputs));
                    EXPECT_EQ(
                        bytes32_t(exec_events.txn_inputs[i]->txn_hash),
                        to_bytes(hash))
                        << name;
                }
            }

            // Generate a witness from execution against ptdb_gen, encode
            // it, parse it back, reconstruct a fresh PartialTrieDb, and
            // re-execute the block against the reconstructed db. This
            // validates that the witness contains enough information to
            // replay the block with no HashStub hits, and that the
            // resulting state root matches the full-TrieDb execution.
            if (ptdb_gen.has_value()) {
                bytes32_t const pre_state_root = ptdb_gen->state_root();
                WitnessData witness_data;
                std::vector<Receipt> receipts_gen;
                std::vector<std::vector<CallFrame>> call_frames_gen;
                TrackingBlockHashBuffer tracking_buf{block_hash_buffer};
                // Fresh vm per block. Must start with an empty varcode
                // cache so BlockState::read_code falls through to
                // ptdb_gen->read_code for every pre-state contract loaded
                // this block, letting loaded_codes_ observe the load. A
                // shared vm across blocks would cache codes in block N
                // and short-circuit block N+1's reads.
                vm::VM vm_gen;
                gen_tracker.reset();
                auto const gen_result = execute<traits>(
                    block.value(),
                    *ptdb_gen,
                    vm_gen,
                    tracking_buf,
                    senders_and_authorities_map_gen,
                    /*enable_tracing=*/false,
                    receipts_gen,
                    call_frames_gen,
                    [&](StateDeltas const &deltas) {
                        witness_data = ptdb_gen->collect_witness(deltas);
                    });
                EXPECT_TRUE(gen_result.has_value())
                    << "witness-gen execution failed for " << name << " block "
                    << curr_block_number << ": "
                    << (gen_result.has_error()
                            ? gen_result.error().message().c_str()
                            : "");

                if (gen_result.has_value()) {
                    bytes32_t const post_state_root = ptdb_gen->state_root();

                    // Materialise bytecodes from the deduped intercode
                    // set directly — no second db lookup needed since
                    // read_code already stored the SharedIntercode.
                    std::vector<byte_string> codes_vec;
                    codes_vec.reserve(witness_data.codes.size());
                    for (auto const &intercode : witness_data.codes) {
                        auto const span = intercode->code_span();
                        codes_vec.emplace_back(span.begin(), span.end());
                    }

                    // Ancestor headers: [lowest..N), where `lowest` is the
                    // minimum block number queried via BLOCKHASH, or N-1
                    // (parent only) if BLOCKHASH was never called.
                    uint64_t const lowest = tracking_buf.min_queried().value_or(
                        curr_block_number - 1);
                    MONAD_ASSERT(lowest < curr_block_number);
                    MONAD_ASSERT(
                        ancestor_headers_gen.size() >= curr_block_number);
                    std::vector<byte_string> const headers_slice(
                        ancestor_headers_gen.begin() +
                            static_cast<ptrdiff_t>(lowest),
                        ancestor_headers_gen.begin() +
                            static_cast<ptrdiff_t>(curr_block_number));

                    byte_string const witness_bytes = encode_execution_witness(
                        block_rlp,
                        pre_state_root,
                        post_state_root,
                        witness_data.nodes,
                        codes_vec,
                        headers_slice);

                    // Parse the witness back and reconstruct a fresh
                    // PartialTrieDb from it.
                    auto const parsed = parse_execution_witness(witness_bytes);
                    ASSERT_TRUE(parsed.has_value())
                        << "generated witness failed to parse for " << name
                        << " block " << curr_block_number;

                    auto rebuilt =
                        PartialTrieDb<NoopAccessTracker>::from_reth_witness(
                            parsed.value().pre_state_root,
                            parsed.value().encoded_nodes,
                            parsed.value().encoded_codes);
                    ASSERT_TRUE(rebuilt.has_value())
                        << "from_reth_witness failed for " << name << " block "
                        << curr_block_number << ": "
                        << rebuilt.error().message().c_str();

                    // Rebuild a BlockHashBuffer from the ancestor headers
                    // carried in the witness. The re-execution must only
                    // see what the witness encodes.
                    BlockHashBufferFinalized rebuilt_buf;
                    byte_string_view headers_view =
                        parsed.value().encoded_headers;
                    while (!headers_view.empty()) {
                        auto const payload_result =
                            rlp::parse_string_metadata(headers_view);
                        ASSERT_TRUE(payload_result.has_value())
                            << "ancestor header rlp parse failed for " << name
                            << " block " << curr_block_number;
                        byte_string_view const payload = payload_result.value();
                        byte_string_view header_enc = payload;
                        auto decoded_header =
                            rlp::decode_block_header(header_enc);
                        ASSERT_TRUE(decoded_header.has_value())
                            << "ancestor header decode failed for " << name
                            << " block " << curr_block_number;
                        bytes32_t const hash = to_bytes(keccak256(payload));
                        rebuilt_buf.set(decoded_header.value().number, hash);
                    }

                    std::vector<Receipt> receipts_reexec;
                    std::vector<std::vector<CallFrame>> call_frames_reexec;
                    auto const reexec_result = execute<traits>(
                        block.value(),
                        rebuilt.value(),
                        vm_reexec,
                        rebuilt_buf,
                        senders_and_authorities_map_gen,
                        /*enable_tracing=*/false,
                        receipts_reexec,
                        call_frames_reexec);
                    EXPECT_TRUE(reexec_result.has_value())
                        << "witness round-trip execution failed for " << name
                        << " block " << curr_block_number << ": "
                        << (reexec_result.has_error()
                                ? reexec_result.error().message().c_str()
                                : "");

                    if (reexec_result.has_value()) {
                        EXPECT_EQ(
                            rebuilt.value().state_root(), tdb.state_root())
                            << "post-state root mismatch (round-trip) for "
                            << name << " block " << curr_block_number;
                    }
                }

                ancestor_headers_gen.push_back(
                    rlp::encode_block_header(block.value().header));
            }
        }
        else {
            // Error case: if this test failed unexpectedly, then serialize the
            // db state such that we can dump it for inspection.
            if (!j_block.contains("expectException")) {
                db_post_state = tdb.to_json();
            }
            EXPECT_TRUE(j_block.contains("expectException"))
                << name << "\n"
                << result.error().message().c_str();
            if (check_exec_events) {
                EXPECT_TRUE(
                    exec_events.block_reject_code ||
                    exec_events.txn_reject_code)
                    << name;
            }
        }
    }

    bool const has_post_state = j_contents.contains("postState");
    bool const has_post_state_hash = j_contents.contains("postStateHash");
    ASSERT_TRUE(has_post_state || has_post_state_hash)
        << "Test fixture missing postState/postStateHash: " << name;

    if (has_post_state_hash) {
        EXPECT_EQ(
            tdb.state_root(), j_contents.at("postStateHash").get<bytes32_t>())
            << name;
    }

    if (has_post_state) {
        validate_post_state(j_contents.at("postState"), db_post_state);
    }
    LOG_DEBUG("post_state: {}", db_post_state.dump());
}

void process_test(
    std::variant<evmc_revision, monad_revision> const &revision,
    std::string const &name, nlohmann::json const &j_contents,
    bool const enable_tracing, bool const witness_roundtrip)
{
    if (std::holds_alternative<evmc_revision>(revision)) {
        auto const rev = std::get<evmc_revision>(revision);
        MONAD_ASSERT(rev != EVMC_CONSTANTINOPLE);
        SWITCH_EVM_TRAITS(
            process_test, name, j_contents, enable_tracing, witness_roundtrip);
    }
    else {
        auto const rev = std::get<monad_revision>(revision);
        SWITCH_MONAD_TRAITS(
            process_test, name, j_contents, enable_tracing, witness_roundtrip);
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

void BlockchainTest::SetUpTestSuite()
{
    pool_ = new fiber::PriorityPool{1, 1};
    ASSERT_TRUE(monad::init_trusted_setup());
}

void BlockchainTest::TearDownTestSuite()
{
    delete pool_;
    pool_ = nullptr;
}

void BlockchainTest::TestBody()
{
    std::ifstream f{file_};

    auto const json = nlohmann::json::parse(f);
    bool executed = false;
    for (auto const &[name, j_contents] : json.items()) {
        auto const network = j_contents.at("network").get<std::string>();
        if (!revision_map.contains(network)) {
            LOG_ERROR(
                "Skipping {} due to missing support for network {}",
                name,
                network);
            continue;
        }

        auto const &rev = revision_map.at(network);
        if (revision_.has_value() && rev != revision_) {
            continue;
        }

        executed = true;

        process_test(
            rev, name, j_contents, enable_tracing_, witness_roundtrip_);
    }

    if (!executed && revision_.has_value()) {
        std::visit(
            [](auto const &r) {
                GTEST_SKIP() << "no test cases found for revision=" << r;
            },
            revision_.value());
    }
}

void register_blockchain_tests_path(
    std::filesystem::path const &root,
    std::optional<std::variant<evmc_revision, monad_revision>> const &revision,
    bool const enable_tracing, bool const witness_roundtrip)
{
    namespace fs = std::filesystem;
    MONAD_ASSERT(fs::exists(root));

    auto register_test = [&root, &revision, enable_tracing, witness_roundtrip](
                             fs::path const &path) {
        if (path.extension() == ".json") {
            MONAD_ASSERT(fs::is_regular_file(path));

            auto test_name = path == root ? path.filename().string()
                                          : fs::relative(path, root).string();
            // get rid of minus signs, which is a special symbol when used in
            // filtering
            std::ranges::replace(test_name, '-', '_');

            testing::RegisterTest(
                "BlockchainTests",
                test_name.c_str(),
                nullptr,
                nullptr,
                path.string().c_str(),
                0,
                [=] {
                    return new test::BlockchainTest(
                        path, revision, enable_tracing, witness_roundtrip);
                });
        }
    };

    if (fs::is_directory(root)) {
        for (auto const &entry : fs::recursive_directory_iterator{root}) {
            register_test(entry.path());
        }
    }
    else {
        MONAD_ASSERT(fs::is_regular_file(root));
        register_test(root);
    }
}

void register_blockchain_tests(
    std::optional<std::variant<evmc_revision, monad_revision>> const &revision,
    bool const enable_tracing, bool const witness_roundtrip)
{
    // skip slow tests
    testing::FLAGS_gtest_filter +=
        ":-:BlockchainTests.GeneralStateTests/stTimeConsuming/*:"
        "BlockchainTests.GeneralStateTests/VMTests/vmPerformance/*:"
        "BlockchainTests.GeneralStateTests/stQuadraticComplexityTest/"
        "Call50000_sha256.json:"
        "BlockchainTests.ValidBlocks/bcForkStressTest/ForkStressTest.json";

    register_blockchain_tests_path(
        test_resource::ethereum_tests_dir / "BlockchainTests",
        revision,
        enable_tracing,
        witness_roundtrip);
    register_blockchain_tests_path(
        test_resource::internal_blockchain_tests_dir,
        revision,
        enable_tracing,
        witness_roundtrip);
    register_blockchain_tests_path(
        test_resource::build_dir /
            "src/ExecutionSpecTestFixtures/blockchain_tests",
        revision,
        enable_tracing,
        witness_roundtrip);
}

MONAD_TEST_NAMESPACE_END
