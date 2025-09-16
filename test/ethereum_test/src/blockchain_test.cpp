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
#include <ethereum_test.hpp>
#include <event.hpp>
#include <from_json.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/event/event_iterator.h>
#include <category/core/event/event_ring.h>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/exec_iter_help.h>
#include <category/execution/ethereum/event/record_block_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>
#include <quill/detail/LogMacros.h>

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
#include <span>
#include <string>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct EthereumMainnetRev : EthereumMainnet
{
    evmc_revision const rev;

    EthereumMainnetRev(evmc_revision const rev)
        : rev{rev}
    {
    }

    virtual evmc_revision get_revision(
        uint64_t /* block_number */, uint64_t /* timestamp */) const override
    {
        return rev;
    }
};

BlockHeader read_genesis_blockheader(nlohmann::json const &genesis_json)
{
    BlockHeader block_header{};

    block_header.difficulty = intx::from_string<uint256_t>(
        genesis_json["difficulty"].get<std::string>());

    auto const extra_data =
        evmc::from_hex(genesis_json["extraData"].get<std::string>());
    MONAD_ASSERT(extra_data.has_value());
    block_header.extra_data = extra_data.value();

    block_header.gas_limit =
        std::stoull(genesis_json["gasLimit"].get<std::string>(), nullptr, 0);

    auto const mix_hash_byte_string =
        evmc::from_hex(genesis_json["mixHash"].get<std::string>());
    MONAD_ASSERT(mix_hash_byte_string.has_value());
    std::copy_n(
        mix_hash_byte_string.value().begin(),
        mix_hash_byte_string.value().length(),
        block_header.prev_randao.bytes);

    uint64_t const nonce{
        std::stoull(genesis_json["nonce"].get<std::string>(), nullptr, 0)};
    intx::be::unsafe::store<uint64_t>(block_header.nonce.data(), nonce);

    auto const parent_hash_byte_string =
        evmc::from_hex(genesis_json["parentHash"].get<std::string>());
    MONAD_ASSERT(parent_hash_byte_string.has_value());
    std::copy_n(
        parent_hash_byte_string.value().begin(),
        parent_hash_byte_string.value().length(),
        block_header.parent_hash.bytes);

    block_header.timestamp =
        std::stoull(genesis_json["timestamp"].get<std::string>(), nullptr, 0);

    if (genesis_json.contains("coinbase")) {
        auto const coinbase =
            evmc::from_hex(genesis_json["coinbase"].get<std::string>());
        MONAD_ASSERT(coinbase.has_value());
        std::copy_n(
            coinbase.value().begin(),
            coinbase.value().length(),
            block_header.beneficiary.bytes);
    }

    // London fork
    if (genesis_json.contains("baseFeePerGas")) {
        block_header.base_fee_per_gas = intx::from_string<uint256_t>(
            genesis_json["baseFeePerGas"].get<std::string>());
    }

    // Shanghai fork
    if (genesis_json.contains("blobGasUsed")) {
        block_header.blob_gas_used = std::stoull(
            genesis_json["blobGasUsed"].get<std::string>(), nullptr, 0);
    }
    if (genesis_json.contains("excessBlobGas")) {
        block_header.excess_blob_gas = std::stoull(
            genesis_json["excessBlobGas"].get<std::string>(), nullptr, 0);
    }
    if (genesis_json.contains("parentBeaconBlockRoot")) {
        auto const parent_beacon_block_root = evmc::from_hex(
            genesis_json["parentBeaconBlockRoot"].get<std::string>());
        MONAD_ASSERT(parent_beacon_block_root.has_value());
        auto &write_to =
            block_header.parent_beacon_block_root.emplace(bytes32_t{});
        std::copy_n(
            parent_beacon_block_root.value().begin(),
            parent_beacon_block_root.value().length(),
            write_to.bytes);
    }

    // Prague fork
    if (genesis_json.contains("requestsHash")) {
        auto const requests_hash =
            evmc::from_hex(genesis_json["requestsHash"].get<std::string>());
        MONAD_ASSERT(requests_hash.has_value());
        auto &write_to = block_header.requests_hash.emplace(bytes32_t{});
        std::copy_n(
            requests_hash.value().begin(),
            requests_hash.value().length(),
            write_to.bytes);
    }

    return block_header;
}

void register_tests(
    std::filesystem::path const &root,
    std::optional<evmc_revision> const &revision, bool enable_tracing)
{
    namespace fs = std::filesystem;
    MONAD_ASSERT(fs::exists(root) && fs::is_directory(root));

    for (auto const &entry : fs::recursive_directory_iterator{root}) {
        auto const path = entry.path();
        if (path.extension() == ".json") {
            MONAD_ASSERT(entry.is_regular_file());

            // get rid of minus signs, which is a special symbol when used in //
            // filtering
            auto test = fmt::format("{}", fs::relative(path, root).string());
            std::ranges::replace(test, '-', '_');

            testing::RegisterTest(
                "BlockchainTests",
                test.c_str(),
                nullptr,
                nullptr,
                path.string().c_str(),
                0,
                [=] {
                    return new test::BlockchainTest(
                        path, revision, enable_tracing);
                });
        }
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

template <Traits traits>
Result<std::vector<Receipt>> BlockchainTest::execute_and_record(
    Block &block, test::db_t &db, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer, bool enable_tracing)
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
Result<BlockExecOutput> BlockchainTest::execute(
    Block &block, test::db_t &db, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer, bool enable_tracing,
    std::vector<Receipt> &receipts,
    std::vector<std::vector<CallFrame>> &call_frames)
{
    using namespace monad::test;

    BOOST_OUTCOME_TRY(static_validate_block<traits>(block));

    BlockState block_state(db, vm);
    BlockMetrics metrics;
    EthereumMainnetRev const chain{traits::evm_rev()};
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
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        call_tracers[i] =
            enable_tracing
                ? std::unique_ptr<CallTracerBase>{std::make_unique<CallTracer>(
                      block.transactions[i], call_frames[i])}
                : std::unique_ptr<CallTracerBase>{
                      std::make_unique<NoopCallTracer>()};
    }

    BOOST_OUTCOME_TRY(
        receipts,
        execute_block<traits>(
            chain,
            block,
            senders,
            recovered_authorities,
            block_state,
            block_hash_buffer,
            *pool_,
            metrics,
            call_tracers));

    block_state.log_debug();
    block_state.commit(
        bytes32_t{block.header.number},
        block.header,
        receipts,
        std::vector<std::vector<CallFrame>>{block.transactions.size()},
        senders,
        block.transactions,
        block.ommers,
        block.withdrawals);
    db.finalize(block.header.number, bytes32_t{block.header.number});

    BlockExecOutput exec_output;
    exec_output.eth_header = db.read_eth_header();
    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));

    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, exec_output.eth_header));

    return exec_output;
}

Result<std::vector<Receipt>> BlockchainTest::execute_dispatch(
    evmc_revision const rev, Block &block, test::db_t &db, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer, bool enable_tracing)
{
    MONAD_ASSERT(rev != EVMC_CONSTANTINOPLE);
    SWITCH_EVM_TRAITS(
        execute_and_record, block, db, vm, block_hash_buffer, enable_tracing);
    MONAD_ASSERT(false);
}

void BlockchainTest::validate_post_state(
    nlohmann::json const &json, nlohmann::json const &db)
{
    EXPECT_EQ(db.size(), json.size());

    for (auto const &[addr, j_account] : json.items()) {
        nlohmann::json const addr_json = addr;
        auto const addr_bytes = addr_json.get<Address>();
        auto const hashed_account = to_bytes(keccak256(addr_bytes.bytes));
        auto const db_addr_key = fmt::format("{}", hashed_account);

        ASSERT_TRUE(db.contains(db_addr_key)) << db_addr_key;
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
            << db_addr_key;
        EXPECT_EQ(db_account.at("nonce").get<std::string>(), expected_nonce)
            << db_addr_key;
        EXPECT_EQ(db_account.at("code").get<std::string>(), expected_code)
            << db_addr_key;

        auto const &db_storage = db_account.at("storage");
        EXPECT_EQ(db_storage.size(), j_account.at("storage").size())
            << db_addr_key;
        for (auto const &[key, j_value] : j_account.at("storage").items()) {
            nlohmann::json const key_json = key;
            auto const key_bytes = key_json.get<bytes32_t>();
            auto const db_storage_key =
                fmt::format("{}", to_bytes(keccak256(key_bytes.bytes)));
            ASSERT_TRUE(db_storage.contains(db_storage_key)) << db_storage_key;
            auto const expected_value =
                fmt::format("{}", j_value.get<bytes32_t>());
            EXPECT_EQ(db_storage.at(db_storage_key).at("value"), expected_value)
                << db_storage_key;
        }
    }
}

fiber::PriorityPool *BlockchainTest::pool_ = nullptr;

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

        auto const rev = revision_map.at(network);
        if (revision_.has_value() && rev != revision_) {
            continue;
        }

        executed = true;

        InMemoryMachine machine;
        mpt::Db db{machine};
        db_t tdb{db};
        vm::VM vm;
        {
            auto const genesisJson = j_contents.at("genesisBlockHeader");
            auto header = read_genesis_blockheader(genesisJson);
            ASSERT_EQ(
                NULL_ROOT,
                evmc::from_hex<bytes32_t>(
                    genesisJson.at("transactionsTrie").get<std::string>())
                    .value());
            ASSERT_EQ(
                NULL_ROOT,
                evmc::from_hex<bytes32_t>(
                    genesisJson.at("receiptTrie").get<std::string>())
                    .value());
            ASSERT_EQ(
                NULL_LIST_HASH,
                evmc::from_hex<bytes32_t>(
                    genesisJson.at("uncleHash").get<std::string>())
                    .value());
            ASSERT_EQ(
                bytes32_t{},
                evmc::from_hex<bytes32_t>(
                    genesisJson.at("parentHash").get<std::string>())
                    .value());

            std::optional<std::vector<Withdrawal>> withdrawals;
            if (rev >= EVMC_SHANGHAI) {
                ASSERT_EQ(
                    NULL_ROOT,
                    evmc::from_hex<bytes32_t>(
                        genesisJson.at("withdrawalsRoot").get<std::string>())
                        .value());
                withdrawals.emplace(std::vector<Withdrawal>{});
            }

            BlockState bs{tdb, vm};
            State state{bs, Incarnation{0, 0}};
            load_state_from_json(j_contents.at("pre"), state);
            bs.merge(state);
            bs.commit(
                NULL_HASH_BLAKE3,
                header,
                {} /* receipts */,
                {} /* call frames */,
                {} /* senders */,
                {} /* transactions */,
                {} /* ommers */,
                withdrawals);
            tdb.finalize(0, NULL_HASH_BLAKE3);
            ASSERT_EQ(
                to_bytes(
                    keccak256(rlp::encode_block_header(tdb.read_eth_header()))),
                evmc::from_hex<bytes32_t>(
                    genesisJson.at("hash").get<std::string>())
                    .value());
        }
        auto db_post_state = tdb.to_json();

        BlockHashBufferFinalized block_hash_buffer;
        for (auto const &j_block : j_contents.at("blocks")) {

            auto const block_rlp = j_block.at("rlp").get<byte_string>();
            byte_string_view block_rlp_view{block_rlp};
            auto block = rlp::decode_block(block_rlp_view);
            if (block.has_error() || !block_rlp_view.empty()) {
                EXPECT_TRUE(j_block.contains("expectException")) << name;
                continue;
            }

            if (block.value().header.number == 0) {
                EXPECT_TRUE(j_block.contains("expectException"));
                continue;
            }
            if (j_block.contains("blocknumber") &&
                block.value().header.number !=
                    std::stoull(j_block.at("blocknumber").get<std::string>())) {
                EXPECT_TRUE(j_block.contains("expectException"));
                continue;
            }

            block_hash_buffer.set(
                block.value().header.number - 1,
                block.value().header.parent_hash);

            uint64_t const curr_block_number = block.value().header.number;
            auto const result = execute_dispatch(
                rev,
                block.value(),
                tdb,
                vm,
                block_hash_buffer,
                enable_tracing_);

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
                EXPECT_FALSE(j_block.contains("expectException"));
                EXPECT_EQ(tdb.state_root(), block.value().header.state_root)
                    << name;
                EXPECT_EQ(
                    tdb.transactions_root(),
                    block.value().header.transactions_root)
                    << name;
                EXPECT_EQ(
                    tdb.withdrawals_root(),
                    block.value().header.withdrawals_root)
                    << name;
                auto const encoded_ommers_res = db.get(
                    mpt::concat(FINALIZED_NIBBLE, OMMER_NIBBLE),
                    curr_block_number);
                auto const tdb_ommers_hash =
                    to_bytes(keccak256(encoded_ommers_res.value()));
                EXPECT_TRUE(encoded_ommers_res.has_value());
                EXPECT_EQ(tdb_ommers_hash, block.value().header.ommers_hash);
                if (rev >= EVMC_BYZANTIUM) {
                    EXPECT_EQ(
                        tdb.receipts_root(), block.value().header.receipts_root)
                        << name;
                }
                EXPECT_EQ(
                    result.value().size(), block.value().transactions.size())
                    << name;

                if (check_exec_events) {
                    EXPECT_FALSE(exec_events.block_reject_code);
                    EXPECT_EQ(
                        exec_events.block_end->exec_output.state_root,
                        tdb.state_root());
                    EXPECT_EQ(
                        exec_events.block_start->eth_block_input
                            .transactions_root,
                        tdb.transactions_root());
                    if (tdb.withdrawals_root()) {
                        EXPECT_EQ(
                            exec_events.block_start->eth_block_input
                                .withdrawals_root,
                            *tdb.withdrawals_root());
                    }
                    else {
                        EXPECT_EQ(
                            exec_events.block_start->eth_block_input
                                .withdrawals_root,
                            bytes32_t{});
                    }
                    EXPECT_EQ(
                        exec_events.block_start->eth_block_input.ommers_hash,
                        tdb_ommers_hash);
                    if (rev >= EVMC_BYZANTIUM) {
                        EXPECT_EQ(
                            exec_events.block_end->exec_output.receipts_root,
                            tdb.receipts_root());
                    }
                    EXPECT_EQ(
                        exec_events.block_start->eth_block_input.txn_count,
                        result.value().size());
                }

                { // verify block header is stored correctly
                    auto res = db.get(
                        mpt::concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE),
                        curr_block_number);
                    EXPECT_TRUE(res.has_value());
                    auto const decode_res =
                        rlp::decode_block_header(res.value());
                    EXPECT_TRUE(decode_res.has_value());
                    auto const decoded_block_header = decode_res.value();
                    EXPECT_EQ(decode_res.value(), block.value().header);
                }
                { // look up block hash
                    auto const block_hash = keccak256(
                        rlp::encode_block_header(block.value().header));
                    auto res = db.get(
                        mpt::concat(
                            FINALIZED_NIBBLE,
                            BLOCK_HASH_NIBBLE,
                            mpt::NibblesView{block_hash}),
                        curr_block_number);
                    EXPECT_TRUE(res.has_value());
                    auto const decoded_number =
                        rlp::decode_unsigned<uint64_t>(res.value());
                    EXPECT_TRUE(decoded_number.has_value());
                    EXPECT_EQ(decoded_number.value(), curr_block_number);
                }
                // verify tx hash
                for (unsigned i = 0; i < block.value().transactions.size();
                     ++i) {
                    auto const &tx = block.value().transactions[i];
                    auto const hash = keccak256(rlp::encode_transaction(tx));
                    auto tx_hash_res = db.get(
                        mpt::concat(
                            FINALIZED_NIBBLE,
                            TX_HASH_NIBBLE,
                            mpt::NibblesView{hash}),
                        curr_block_number);
                    EXPECT_TRUE(tx_hash_res.has_value());
                    EXPECT_EQ(
                        tx_hash_res.value(),
                        rlp::encode_list2(
                            rlp::encode_unsigned(curr_block_number),
                            rlp::encode_unsigned(i)));

                    if (check_exec_events) {
                        ASSERT_LT(i, size(exec_events.txn_inputs));
                        EXPECT_EQ(
                            exec_events.txn_inputs[i]->txn_hash,
                            to_bytes(hash));
                    }
                }
            }
            else {
                EXPECT_TRUE(j_block.contains("expectException"))
                    << result.error().message().c_str();
                if (check_exec_events) {
                    EXPECT_TRUE(
                        exec_events.block_reject_code ||
                        exec_events.txn_reject_code);
                }
            }
        }

        bool const has_post_state = j_contents.contains("postState");
        bool const has_post_state_hash = j_contents.contains("postStateHash");
        MONAD_DEBUG_ASSERT(has_post_state || has_post_state_hash);

        if (has_post_state_hash) {
            EXPECT_EQ(
                tdb.state_root(),
                j_contents.at("postStateHash").get<bytes32_t>());
        }

        if (has_post_state) {
            validate_post_state(j_contents.at("postState"), db_post_state);
        }
        LOG_DEBUG("post_state: {}", db_post_state.dump());
    }

    if (!executed) {
        MONAD_ASSERT(revision_.has_value());
        GTEST_SKIP() << "no test cases found revision=" << revision_.value();
    }
}

void register_blockchain_tests(
    std::optional<evmc_revision> const &revision, bool enable_tracing)
{
    // skip slow tests
    testing::FLAGS_gtest_filter +=
        ":-:BlockchainTests.GeneralStateTests/stTimeConsuming/*:"
        "BlockchainTests.GeneralStateTests/VMTests/vmPerformance/*:"
        "BlockchainTests.GeneralStateTests/stQuadraticComplexityTest/"
        "Call50000_sha256.json:"
        "BlockchainTests.ValidBlocks/bcForkStressTest/ForkStressTest.json";

    register_tests(
        test_resource::ethereum_tests_dir / "BlockchainTests",
        revision,
        enable_tracing);
    register_tests(
        test_resource::internal_blockchain_tests_dir, revision, enable_tracing);
    register_tests(
        test_resource::build_dir /
            "src/ExecutionSpecTestFixtures/blockchain_tests",
        revision,
        enable_tracing);
    register_tests(
        test_resource::build_dir /
            "src/ExecutionSpecTestFixturesFusakaDevnet/blockchain_tests",
        revision,
        enable_tracing);
}

MONAD_TEST_NAMESPACE_END
