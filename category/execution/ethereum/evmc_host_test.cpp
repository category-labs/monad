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

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/mpt/node_cache.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/util.hpp>
#include <category/vm/vm.hpp>

#include <monad/test/traits_test.hpp>

#include <test_resource_data.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <filesystem>
#include <string>

#include <unistd.h>

using namespace monad;

using db_t = TrieDb;

bool operator==(evmc_tx_context const &lhs, evmc_tx_context const &rhs)
{
    return !std::memcmp(
               lhs.tx_gas_price.bytes,
               rhs.tx_gas_price.bytes,
               sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.tx_origin.bytes,
               rhs.tx_origin.bytes,
               sizeof(evmc_address)) &&
           !std::memcmp(
               lhs.block_coinbase.bytes,
               rhs.block_coinbase.bytes,
               sizeof(evmc_address)) &&
           lhs.block_number == rhs.block_number &&
           lhs.block_timestamp == rhs.block_timestamp &&
           lhs.block_gas_limit == rhs.block_gas_limit &&
           !std::memcmp(
               lhs.block_prev_randao.bytes,
               rhs.block_prev_randao.bytes,
               sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.chain_id.bytes, rhs.chain_id.bytes, sizeof(evmc_bytes32)) &&
           !std::memcmp(
               lhs.block_base_fee.bytes,
               rhs.block_base_fee.bytes,
               sizeof(evmc_bytes32)) &&
           lhs.block_round == rhs.block_round;
}

TYPED_TEST(TraitsTest, get_tx_context)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto bene{
        0xbebebebebebebebebebebebebebebebebebebebe_address};
    static uint64_t const chain_id{1};
    static uint256_t const base_fee_per_gas{37'000'000'000};
    static uint256_t const gas_cost = 37'000'000'000;

    BlockHeader hdr{
        .prev_randao =
            0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32,
        .difficulty = 10'000'000u,
        .number = 15'000'000,
        .gas_limit = 50'000,
        .timestamp = 1677616016,
        .beneficiary = bene,
        .base_fee_per_gas = base_fee_per_gas,
    };
    Transaction const tx{
        .sc = {.chain_id = chain_id}, .max_fee_per_gas = base_fee_per_gas};

    auto const result = get_tx_context<typename TestFixture::Trait>(
        tx, from, hdr, 1, default_blob_schedule<typename TestFixture::Trait>());
    evmc_tx_context ctx{
        .tx_origin = from,
        .block_coinbase = bene,
        .block_number = 15'000'000,
        .block_timestamp = 1677616016,
        .block_gas_limit = 50'000,
        .block_prev_randao = evmc::uint256be{10'000'000u},
    };
    ctx.chain_id = store_be_as<evmc::uint256be>(uint256_t{chain_id});
    ctx.tx_gas_price = store_be_as<evmc::uint256be>(gas_cost);
    ctx.block_base_fee = store_be_as<evmc::uint256be>(base_fee_per_gas);
    EXPECT_EQ(result, ctx);

    hdr.difficulty = 0;
    auto const pos_result = get_tx_context<typename TestFixture::Trait>(
        tx, from, hdr, 1, default_blob_schedule<typename TestFixture::Trait>());
    std::memcpy(
        ctx.block_prev_randao.bytes,
        hdr.prev_randao.bytes,
        sizeof(hdr.prev_randao));
    EXPECT_EQ(pos_result, ctx);

    // slot_number (EIP-7843) is surfaced as block_round (unset -> 0 is
    // covered by the comparisons above).
    hdr.slot_number = 9'000'000'000;
    EXPECT_EQ(
        get_tx_context<typename TestFixture::Trait>(
            tx,
            from,
            hdr,
            1,
            default_blob_schedule<typename TestFixture::Trait>())
            .block_round,
        uint64_t{9'000'000'000});
}

TYPED_TEST(TraitsTest, emit_log)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto topic0{
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32};
    static constexpr auto topic1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr evmc::bytes32 topics[] = {topic0, topic1};
    static byte_string const data = {0x00, 0x01, 0x02, 0x03, 0x04};

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    trace::StateTracer noop_state_tracer = std::monostate{};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer,
        noop_state_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        tx,
        base_fee,
        0,
        chain_ctx};

    host.emit_log(from, data.data(), data.size(), topics, std::size(topics));

    auto const logs = state.logs();
    EXPECT_EQ(logs.size(), 1);
    EXPECT_EQ(logs[0].address, from);
    EXPECT_EQ(logs[0].data, data);
    EXPECT_EQ(logs[0].topics.size(), 2);
    EXPECT_EQ(logs[0].topics[0], topic0);
    EXPECT_EQ(logs[0].topics[1], topic1);
}

TYPED_TEST(TraitsTest, access_precompile)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    Transaction tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t base_fee{0};
    trace::StateTracer noop_state_tracer = std::monostate{};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer,
        noop_state_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        tx,
        base_fee,
        0,
        chain_ctx};

    EXPECT_EQ(
        host.access_account(0x0000000000000000000000000000000000000001_address),
        EVMC_ACCESS_WARM);
    EXPECT_EQ(
        host.access_account(0x5353535353535353535353535353535353535353_address),
        EVMC_ACCESS_COLD);
}

TEST(EvmcHostTest, host_methods_rethrow_pruned_read)
{
    using traits = MonadTraits<MONAD_NEXT>;

    std::string dbpath = (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                          "evmc_host_pruned_read_XXXXXX")
                             .string();
    int const fd = ::mkstemp(dbpath.data());
    ASSERT_NE(fd, -1);
    ASSERT_NE(
        ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)), -1);
    ::close(fd);

    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            mpt::OnDiskDbConfig{
                .append = false,
                .dbname_path = dbpath,
                .fixed_history_length = mpt::MIN_HISTORY_LENGTH,
                .chunk_capacity = 24}};
        TrieDb write_db{db};
        Address const beneficiary =
            0x5353535353535353535353535353535353535353_address;
        StateDeltas initial_state{
            {beneficiary,
             StateDelta{
                 .account = {
                     std::nullopt, Account{.balance = 1, .nonce = 0}}}}};

        monad::test::commit_sequential(
            write_db, std::move(initial_state), {}, BlockHeader{.number = 0});
        for (uint64_t block = 1; block < mpt::MIN_HISTORY_LENGTH; ++block) {
            monad::test::commit_sequential(
                write_db, {}, {}, BlockHeader{.number = block});
        }

        mpt::RODb read_db{mpt::ReadOnlyOnDiskDbConfig{
            .dbname_path = dbpath,
            .node_lru_max_mem = 1024 * mpt::NodeCache::AVERAGE_NODE_SIZE}};
        TrieRODb stale_db{read_db};
        stale_db.set_block_and_prefix(0);

        monad::test::commit_sequential(
            write_db, {}, {}, BlockHeader{.number = mpt::MIN_HISTORY_LENGTH});
        ASSERT_EQ(db.get_earliest_version(), 1);

        vm::VM vm;
        BlockState block_state{stale_db, vm};
        State state{block_state, Incarnation{0, 0}};
        BlockHashBufferFinalized const block_hash_buffer;
        NoopCallTracer call_tracer;
        Transaction tx{};
        auto const chain_ctx = ChainContext<traits>::debug_empty();
        trace::StateTracer noop_state_tracer = std::monostate{};
        EvmcHost<traits> host{
            call_tracer,
            noop_state_tracer,
            EMPTY_TX_CONTEXT,
            block_hash_buffer,
            state,
            tx,
            uint256_t{0},
            0,
            chain_ctx};

        auto const expect_pruned_read = [](auto &&operation) {
            try {
                operation();
                FAIL() << "expected the pruned read to throw";
            }
            catch (MonadException const &e) {
                EXPECT_STREQ(
                    e.message(),
                    "Block was invalidated in db while execution was in "
                    "progress");
            }
        };

        expect_pruned_read([&] { (void)host.access_account(beneficiary); });
        uint8_t buffer[1]{};
        expect_pruned_read([&] {
            (void)host.copy_code(beneficiary, 0, buffer, sizeof(buffer));
        });
    }

    std::filesystem::remove(dbpath);
}
