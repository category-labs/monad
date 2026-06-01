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
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/db/witness_generator.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/exec_iter_help.h>
#include <category/execution/ethereum/event/record_block_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/evm/monad/revision.h>
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

#include <ankerl/unordered_dense.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <map>
#include <optional>
#include <set>
#include <span>
#include <string>
#include <variant>
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
    std::function<void(
        StateDeltas const &,
        ankerl::unordered_dense::segmented_map<
            bytes32_t, vm::SharedIntercode> const &,
        SelfDestructStorageReads const &)> const &on_pre_commit = {})
{
    static_assert(traits::evm_rev() > EVMC_BYZANTIUM);

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
    // When a pre-commit hook is installed (witness round-trip), record
    // every bytecode the EVM reads during the block via CodeTracer so we
    // can hand the consumer a complete `read_codes` map. Otherwise stay
    // on the zero-cost `std::monostate` path.
    bool const collect_read_codes = static_cast<bool>(on_pre_commit);
    auto make_state_tracer = [collect_read_codes] {
        return collect_read_codes
                   ? std::make_unique<trace::StateTracer>(trace::CodeTracer{})
                   : std::make_unique<trace::StateTracer>(std::monostate{});
    };
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers(
        block.transactions.size());
    trace::StateTracer system_call_state_tracer =
        collect_read_codes ? trace::StateTracer{trace::CodeTracer{}}
                           : trace::StateTracer{std::monostate{}};
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        call_tracers[i] =
            enable_tracing
                ? std::unique_ptr<CallTracerBase>{std::make_unique<CallTracer>(
                      block.transactions[i], call_frames[i])}
                : std::unique_ptr<CallTracerBase>{
                      std::make_unique<NoopCallTracer>()};
        state_tracers[i] = make_state_tracer();
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
            system_call_state_tracer,
            chain_context));

    block_state.log_debug();
    auto [state, code, self_destruct_storage_reads] =
        std::move(block_state).release();

    if (on_pre_commit) {
        // Merge the per-tracer codes maps into a single `read_codes`
        // for the witness consumer. Each per-tx tracer and the
        // system-call tracer holds its own CodeTracer instance under
        // collect_read_codes.
        ankerl::unordered_dense::segmented_map<bytes32_t, vm::SharedIntercode>
            read_codes;
        auto const merge_read_codes = [&](trace::StateTracer const &tracer) {
            auto const *const ct = std::get_if<trace::CodeTracer>(&tracer);
            if (ct == nullptr) {
                return;
            }
            for (auto const &kv : ct->codes) {
                read_codes.emplace(kv.first, kv.second);
            }
        };
        merge_read_codes(system_call_state_tracer);
        for (auto const &tracer : state_tracers) {
            merge_read_codes(*tracer);
        }
        on_pre_commit(*state, read_codes, self_destruct_storage_reads);
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
        std::move(state),
        [&](BlockHeader &h) {
            h.receipts_root = db.receipts_root();
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
    Block &block, Db &db, vm::VM &vm, BlockHashBuffer const &block_hash_buffer,
    std::map<uint64_t, ankerl::unordered_dense::segmented_set<Address>>
        &senders_and_authorities_map,
    bool enable_tracing,
    std::function<void(
        StateDeltas const &,
        ankerl::unordered_dense::segmented_map<
            bytes32_t, vm::SharedIntercode> const &,
        SelfDestructStorageReads const &)> const &on_pre_commit = {})
{
    record_block_start(
        bytes32_t{block.header.number},
        /*chain_id*/ 1,
        block.header,
        block.header.parent_hash,
        block.header.number,
        0,
        uint128_t{block.header.timestamp} * uint128_t{1'000'000'000UL},
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
        call_frames,
        on_pre_commit));
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
    vm::VM::Mode const vm_mode, bool enable_tracing, bool witness_roundtrip,
    std::string const &dump_witnesses_dir)
{
    static_assert(traits::evm_rev() > EVMC_SPURIOUS_DRAGON);

    using namespace test;

    auto const json_state = load_blockchain_json_state<traits>(j_contents);
    auto const test_state = json_state.make_test_state();
    vm::VM vm{vm_mode};
    // Separate vm for witness round-trip re-execution. Pre-loaded codes
    // accumulate across blocks (warm cache), but the round-trip path
    // never touches the live `vm`.
    vm::VM vm_witness;
    mpt::Db &db = test_state->db;
    monad::TrieDb &tdb = test_state->trie_db;

    auto db_post_state = tdb.to_json();

    BlockHashBufferFinalized block_hash_buffer;

    std::map<uint64_t, ankerl::unordered_dense::segmented_set<Address>>
        senders_and_authorities_map{};
    // genesis block has no senders or authorities
    senders_and_authorities_map[0] =
        ankerl::unordered_dense::segmented_set<Address>{};

    std::vector<byte_string> ancestor_headers;
    if (witness_roundtrip && vm_mode == vm::VM::Mode::InterpreterOnly) {
        ancestor_headers.push_back(
            rlp::encode_block_header(tdb.read_eth_header()));
    }

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

        // Witness-only: capture pre-state-root and the touched-set witness
        // via a pre-commit hook; track BLOCKHASH queries to know which
        // ancestor headers belong in the witness.
        TrackingBlockHashBuffer tracking_buf{block_hash_buffer};
        WitnessData witness_data;
        bytes32_t pre_state_root;
        std::function<void(
            StateDeltas const &,
            ankerl::unordered_dense::
                segmented_map<bytes32_t, vm::SharedIntercode> const &,
            SelfDestructStorageReads const &)>
            on_pre_commit;
        if (witness_roundtrip && vm_mode == vm::VM::Mode::InterpreterOnly) {
            on_pre_commit = [&](StateDeltas const &deltas,
                                ankerl::unordered_dense::segmented_map<
                                    bytes32_t,
                                    vm::SharedIntercode> const &read_codes,
                                SelfDestructStorageReads const
                                    &self_destruct_storage_reads) {
                pre_state_root = tdb.state_root();
                auto cursor_res = db.find(
                    tdb.get_root(),
                    mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE),
                    curr_block_number);
                ASSERT_TRUE(cursor_res.has_value())
                    << "state-trie lookup failed while generating witness for "
                    << name << " at block " << curr_block_number;
                witness_data = generate_witness(
                    db,
                    cursor_res.value(),
                    curr_block_number,
                    deltas,
                    read_codes,
                    self_destruct_storage_reads);
            };
        }

        BlockHashBuffer const &exec_buf =
            (witness_roundtrip && vm_mode == vm::VM::Mode::InterpreterOnly)
                ? static_cast<BlockHashBuffer const &>(tracking_buf)
                : static_cast<BlockHashBuffer const &>(block_hash_buffer);

        auto const result = execute_and_record<traits>(
            block.value(),
            tdb,
            vm,
            exec_buf,
            senders_and_authorities_map,
            enable_tracing,
            on_pre_commit);

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
            EXPECT_EQ(tdb.receipts_root(), block.value().header.receipts_root)
                << name;
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
                EXPECT_EQ(
                    bytes32_t(exec_events.block_end->exec_output.receipts_root),
                    tdb.receipts_root())
                    << name;
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

            // Witness round-trip: encode the witness, parse it back,
            // reconstruct a fresh PartialTrieDb, and re-execute the
            // block against it. The post-state root must match the
            // live tdb's.
            if (witness_roundtrip && vm_mode == vm::VM::Mode::InterpreterOnly) {
                uint64_t const lowest =
                    tracking_buf.min_queried().value_or(curr_block_number - 1);
                MONAD_ASSERT(lowest < curr_block_number);
                MONAD_ASSERT(ancestor_headers.size() >= curr_block_number);
                std::vector<byte_string> const headers_slice(
                    ancestor_headers.begin() + static_cast<ptrdiff_t>(lowest),
                    ancestor_headers.begin() +
                        static_cast<ptrdiff_t>(curr_block_number));

                auto const lookup_senders = [&](uint64_t const n)
                    -> ankerl::unordered_dense::segmented_set<Address> const * {
                    auto const it = senders_and_authorities_map.find(n);
                    return it != senders_and_authorities_map.end() ? &it->second
                                                                   : nullptr;
                };
                auto const *const parent_senders =
                    (curr_block_number >= 1)
                        ? lookup_senders(curr_block_number - 1)
                        : nullptr;
                auto const *const grandparent_senders =
                    (curr_block_number >= 2)
                        ? lookup_senders(curr_block_number - 2)
                        : nullptr;

                byte_string const witness_bytes = encode_execution_witness(
                    block_rlp,
                    witness_data.nodes,
                    witness_data.codes,
                    headers_slice,
                    parent_senders,
                    grandparent_senders);

                if (!dump_witnesses_dir.empty()) {
                    std::filesystem::path const dir{dump_witnesses_dir};
                    std::filesystem::create_directories(dir);
                    // Sanitize the test name for use as a filename. The
                    // BlockchainTest hierarchy uses '/' separators in the
                    // gtest test name; flatten to '_'.
                    std::string safe_name = name;
                    for (char &c : safe_name) {
                        if (c == '/' || c == ':' || c == ' ' || c == '(' ||
                            c == ')') {
                            c = '_';
                        }
                    }
                    auto const base =
                        safe_name + "_" + std::to_string(curr_block_number);

                    auto const witness_path = dir / (base + ".witness");
                    std::ofstream out{witness_path, std::ios::binary};
                    out.write(
                        reinterpret_cast<char const *>(witness_bytes.data()),
                        static_cast<std::streamsize>(witness_bytes.size()));

                    // Also drop the live post-state root next to the witness
                    // as a hex string, for manual comparison against what the
                    // zkVM guest emits. The block executed before we got
                    // here, so tdb.state_root() is the post-state.
                    auto const post_root = tdb.state_root();
                    auto const root_path = dir / (base + ".post_state_root");
                    std::ofstream root_out{root_path};
                    root_out << "0x";
                    for (auto const b : post_root.bytes) {
                        root_out << std::hex << std::setw(2)
                                 << std::setfill('0')
                                 << static_cast<unsigned>(b);
                    }
                    root_out << '\n';
                }

                auto const witness = parse_execution_witness(witness_bytes);
                ASSERT_TRUE(witness.has_value())
                    << "generated witness failed to parse for " << name
                    << " block " << curr_block_number;

                auto db_witness = PartialTrieDb::from_witness(
                    pre_state_root,
                    witness.value().encoded_nodes,
                    witness.value().encoded_codes);
                ASSERT_TRUE(db_witness.has_value())
                    << "from_witness failed for " << name << " block "
                    << curr_block_number << ": "
                    << db_witness.error().message().c_str();

                BlockHashBufferFinalized block_hash_buffer_witness;
                byte_string_view headers_view = witness.value().encoded_headers;
                while (!headers_view.empty()) {
                    auto const payload_res =
                        rlp::parse_string_metadata(headers_view);
                    ASSERT_TRUE(payload_res.has_value())
                        << "ancestor header rlp parse failed for " << name
                        << " block " << curr_block_number;
                    byte_string_view const payload = payload_res.value();
                    byte_string_view header_enc = payload;
                    auto decoded_header = rlp::decode_block_header(header_enc);
                    ASSERT_TRUE(decoded_header.has_value())
                        << "ancestor header decode failed for " << name
                        << " block " << curr_block_number;
                    bytes32_t const hash = to_bytes(keccak256(payload));
                    block_hash_buffer_witness.set(
                        decoded_header.value().number, hash);
                }

                std::vector<Receipt> receipts_witness;
                std::vector<std::vector<CallFrame>> call_frames_witness;
                // Fresh per-block map seeded from the witness payload's
                // [4]/[5] address-set fields. execute<>() populates [curr]
                // itself; [curr-1] and [curr-2] are decoded here so
                // ChainContext for Monad traits sees the same membership
                // decisions as the live path.
                std::map<
                    uint64_t,
                    ankerl::unordered_dense::segmented_set<Address>>
                    senders_and_authorities_map_witness{};
                auto const decode_addr_set = [&](byte_string_view list)
                    -> ankerl::unordered_dense::segmented_set<Address> {
                    ankerl::unordered_dense::segmented_set<Address> out;
                    while (!list.empty()) {
                        auto const s = rlp::decode_string(list);
                        MONAD_ASSERT(s.has_value());
                        MONAD_ASSERT(s.value().size() == sizeof(Address));
                        Address a;
                        std::memcpy(a.bytes, s.value().data(), sizeof(Address));
                        out.insert(a);
                    }
                    return out;
                };
                if (curr_block_number >= 1) {
                    senders_and_authorities_map_witness[curr_block_number - 1] =
                        decode_addr_set(witness.value().encoded_parent_senders);
                }
                if (curr_block_number >= 2) {
                    senders_and_authorities_map_witness[curr_block_number - 2] =
                        decode_addr_set(
                            witness.value().encoded_grandparent_senders);
                }
                auto const result_witness = execute<traits>(
                    // assume block was encoded correctly in the witness to
                    // avoid rlp round-trip
                    block.value(),
                    db_witness.value(),
                    vm_witness,
                    block_hash_buffer_witness,
                    senders_and_authorities_map_witness,
                    /*enable_tracing=*/false,
                    receipts_witness,
                    call_frames_witness);
                EXPECT_TRUE(result_witness.has_value())
                    << "witness round-trip execution failed for " << name
                    << " block " << curr_block_number << ": "
                    << (result_witness.has_error()
                            ? result_witness.error().message().c_str()
                            : "");

                if (result_witness.has_value()) {
                    EXPECT_EQ(db_witness.value().state_root(), tdb.state_root())
                        << "post-state root mismatch (round-trip) for " << name
                        << " block " << curr_block_number;
                }

                ancestor_headers.push_back(
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
    vm::VM::Mode const vm_mode, bool const enable_tracing,
    bool const witness_roundtrip, std::string const &dump_witnesses_dir)
{
    if (std::holds_alternative<evmc_revision>(revision)) {
        auto const rev = std::get<evmc_revision>(revision);
        MONAD_ASSERT(rev != EVMC_CONSTANTINOPLE);
        SWITCH_EVM_TRAITS(
            process_test,
            name,
            j_contents,
            vm_mode,
            enable_tracing,
            witness_roundtrip,
            dump_witnesses_dir);
    }
    else {
        auto const rev = std::get<monad_revision>(revision);
        SWITCH_MONAD_TRAITS(
            process_test,
            name,
            j_contents,
            vm_mode,
            enable_tracing,
            witness_roundtrip,
            dump_witnesses_dir);
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

        for (auto const vm_mode : vm::VM::all_modes) {
            if (fixed_vm_mode_.has_value() &&
                fixed_vm_mode_.value() != vm_mode) {
                continue;
            }
            auto const enum_name = vm::VM::mode_to_string(vm_mode);
            auto const full_name = name + "(" + enum_name + " VM mode)";
            process_test(
                rev,
                full_name,
                j_contents,
                vm_mode,
                enable_tracing_,
                witness_roundtrip_,
                dump_witnesses_dir_);
        }
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
    std::optional<vm::VM::Mode> const vm_mode, bool const enable_tracing,
    bool const witness_roundtrip, std::string const &dump_witnesses_dir)
{
    namespace fs = std::filesystem;
    MONAD_ASSERT(fs::exists(root));

    auto register_test = [&root,
                          &revision,
                          vm_mode,
                          enable_tracing,
                          witness_roundtrip,
                          dump_witnesses_dir](fs::path const &path) {
        if (path.extension() == ".json") {
            MONAD_ASSERT(fs::is_regular_file(path));

            auto test_name = path == root ? path.filename().string()
                                          : fs::relative(path, root).string();
            // get rid of minus signs, which is a special symbol when used
            // in filtering
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
                        path,
                        revision,
                        vm_mode,
                        enable_tracing,
                        witness_roundtrip,
                        dump_witnesses_dir);
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
    std::optional<vm::VM::Mode> const vm_mode, bool const enable_tracing,
    bool const witness_roundtrip, std::string const &dump_witnesses_dir)
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
        vm_mode,
        enable_tracing,
        witness_roundtrip,
        dump_witnesses_dir);
    register_blockchain_tests_path(
        test_resource::internal_blockchain_tests_dir,
        revision,
        vm_mode,
        enable_tracing,
        witness_roundtrip,
        dump_witnesses_dir);
    register_blockchain_tests_path(
        test_resource::build_dir /
            "src/ExecutionSpecTestFixtures/blockchain_tests",
        revision,
        vm_mode,
        enable_tracing,
        witness_roundtrip,
        dump_witnesses_dir);
}

MONAD_TEST_NAMESPACE_END
