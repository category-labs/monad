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

#include <test_resource_data.h>

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/storage_status.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/config.hpp>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/future/future.hpp>
#include <boost/fiber/future/promise.hpp>
#include <boost/fiber/operations.hpp>
#include <boost/fiber/type.hpp>

#include <gtest/gtest.h>

#include <atomic>
#include <chrono>
#include <cstdint>
#include <exception>
#include <functional>
#include <future>
#include <memory>
#include <optional>
#include <semaphore>
#include <tuple>
#include <utility>
#include <variant>

MONAD_TEST_NAMESPACE_BEGIN

using namespace literals;

constexpr Address CONTRACT{0xa11ce};
constexpr Address SENDER{0xb0b};
constexpr bytes32_t INPUT_SLOT{0};
constexpr bytes32_t OUTPUT_SLOT{1};

class ObservedDb final : public Db
{
    Db &db_;
    std::function<void()> const on_first_read_;
    std::atomic<bool> observed_{false};

public:
    ObservedDb(Db &db, std::function<void()> on_first_read)
        : db_{db}
        , on_first_read_{std::move(on_first_read)}
    {
    }

    bytes32_t
    read_storage(Address const &address, bytes32_t const &key) override
    {
        auto const value = db_.read_storage(address, key);
        if (address == CONTRACT && key == INPUT_SLOT &&
            !observed_.exchange(true)) {
            on_first_read_();
        }
        return value;
    }

    bool is_page_encoded() const override
    {
        return db_.is_page_encoded();
    }

    std::optional<Account> read_account(Address const &addr) override
    {
        return db_.read_account(addr);
    }

    storage_page_t
    read_storage_page(Address const &addr, bytes32_t const &key) override
    {
        return db_.read_storage_page(addr, key);
    }

    vm::SharedIntercode read_code(bytes32_t const &hash) override
    {
        return db_.read_code(hash);
    }

    BlockHeader read_eth_header() override
    {
        return db_.read_eth_header();
    }

    bytes32_t state_root() override
    {
        return db_.state_root();
    }

    bytes32_t receipts_root() override
    {
        return db_.receipts_root();
    }

    bytes32_t transactions_root() override
    {
        return db_.transactions_root();
    }

    std::optional<bytes32_t> withdrawals_root() override
    {
        return db_.withdrawals_root();
    }

    void set_block_and_prefix(uint64_t const n, bytes32_t const &id) override
    {
        db_.set_block_and_prefix(n, id);
    }

    void finalize(uint64_t const n, bytes32_t const &id) override
    {
        db_.finalize(n, id);
    }

    void update_verified_block(uint64_t const n) override
    {
        db_.update_verified_block(n);
    }

    void update_voted_metadata(uint64_t const n, bytes32_t const &id) override
    {
        db_.update_voted_metadata(n, id);
    }

    void
    update_proposed_metadata(uint64_t const n, bytes32_t const &id) override
    {
        db_.update_proposed_metadata(n, id);
    }

    uint64_t get_block_number() const override
    {
        return db_.get_block_number();
    }

    void commit(
        bytes32_t const &id, CommitBuilder &builder, BlockHeader const &header,
        StateDeltas const &deltas,
        std::function<void(BlockHeader &)> populate_header) override
    {
        db_.commit(id, builder, header, deltas, std::move(populate_header));
    }
};

void seed_contract(
    Db &db, uint64_t const value, byte_string_view const code = {})
{
    auto const code_hash = code.empty() ? NULL_HASH : to_bytes(keccak256(code));
    Code codes;
    if (!code.empty()) {
        codes.emplace(code_hash, vm::make_shared_intercode(code));
    }
    commit_sequential(
        db,
        StateDeltas{
            {CONTRACT,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.code_hash = code_hash, .nonce = 1}},
                 .storage = {{INPUT_SLOT, {bytes32_t{}, bytes32_t{value}}}}}},
            {SENDER,
             StateDelta{
                 .account =
                     {std::nullopt, Account{.balance = 1'000'000'000}}}}},
        codes,
        BlockHeader{});
}

void replace_contract(
    BlockState &block_state, uint64_t const value,
    byte_string_view const code = {})
{
    // Restore identical account fields so incarnation-free validation must
    // detect conflicts through storage values rather than account metadata.
    using Legacy = EvmTraits<MONAD_ETH_SHANGHAI>;
    State deletion{block_state};
    deletion.selfdestruct<Legacy>(CONTRACT, CONTRACT);
    deletion.finalize_account_deletions<Legacy>();
    ASSERT_TRUE(block_state.can_merge(deletion));
    block_state.merge(deletion);

    State recreation{block_state};
    recreation.create_contract(CONTRACT);
    recreation.set_nonce(CONTRACT, 1);
    if (!code.empty()) {
        recreation.set_code(CONTRACT, code);
    }
    if (value != 0) {
        recreation.set_storage(CONTRACT, INPUT_SLOT, bytes32_t{value});
    }
    ASSERT_TRUE(block_state.can_merge(recreation));
    block_state.merge(recreation);
}

using StorageReadCase = std::tuple<uint64_t, uint64_t>;

class StorageResetSpeculationTest
    : public ::testing::TestWithParam<StorageReadCase>
{
};

TEST_P(
    StorageResetSpeculationTest, read_returning_after_reset_cannot_poison_cache)
{
    auto const [before, after] = GetParam();
    std::binary_semaphore read_started{0};
    std::binary_semaphore resume_read{0};
    mpt::Db raw_db{std::make_unique<InMemoryMachine>()};
    TrieDb source_db{raw_db};
    ObservedDb db{source_db, [&] {
                      read_started.release();
                      resume_read.acquire();
                  }};
    seed_contract(db, before);
    vm::VM vm;
    BlockState block_state{db, vm};
    State speculative{block_state};
    ASSERT_EQ(speculative.get_nonce(CONTRACT), 1);

    auto read = std::async(std::launch::async, [&] {
        return speculative.get_storage(CONTRACT, INPUT_SLOT);
    });
    EXPECT_TRUE(read_started.try_acquire_for(std::chrono::seconds{10}));
    replace_contract(block_state, after);
    resume_read.release();

    EXPECT_EQ(read.get(), bytes32_t{before});
    EXPECT_EQ(block_state.read_storage(CONTRACT, INPUT_SLOT), bytes32_t{after});
    EXPECT_EQ(block_state.can_merge(speculative), before == after);

    State retry{block_state};
    EXPECT_EQ(retry.get_nonce(CONTRACT), 1);
    EXPECT_EQ(retry.get_storage(CONTRACT, INPUT_SLOT), bytes32_t{after});
    EXPECT_TRUE(block_state.can_merge(retry));
}

INSTANTIATE_TEST_SUITE_P(
    OldAndReplacementStorage, StorageResetSpeculationTest,
    ::testing::Values(
        StorageReadCase{3, 0}, StorageReadCase{0, 7}, StorageReadCase{3, 3}));

TEST(StorageResetSpeculation, stale_sstore_retries_with_empty_original_storage)
{
    std::binary_semaphore read_started{0};
    std::binary_semaphore resume_read{0};
    mpt::Db raw_db{std::make_unique<InMemoryMachine>()};
    TrieDb source_db{raw_db};
    ObservedDb db{source_db, [&] {
                      read_started.release();
                      resume_read.acquire();
                  }};
    seed_contract(db, 3);
    vm::VM vm;
    BlockState block_state{db, vm};
    State speculative{block_state};
    ASSERT_EQ(speculative.get_nonce(CONTRACT), 1);
    auto write = std::async(std::launch::async, [&] {
        return speculative.set_storage(CONTRACT, INPUT_SLOT, bytes32_t{7});
    });
    EXPECT_TRUE(read_started.try_acquire_for(std::chrono::seconds{10}));
    replace_contract(block_state, 0);
    resume_read.release();

    EXPECT_EQ(write.get(), MONAD_STORAGE_MODIFIED);
    EXPECT_FALSE(block_state.can_merge(speculative));
    State retry{block_state};
    EXPECT_EQ(
        retry.set_storage(CONTRACT, INPUT_SLOT, bytes32_t{7}),
        MONAD_STORAGE_ADDED);
    ASSERT_TRUE(block_state.can_merge(retry));
    block_state.merge(retry);
    EXPECT_EQ(block_state.read_storage(CONTRACT, INPUT_SLOT), bytes32_t{7});
}

TEST(StorageResetSpeculation, repeated_resets_invalidate_zero_reads)
{
    mpt::Db raw_db{std::make_unique<InMemoryMachine>()};
    TrieDb db{raw_db};
    seed_contract(db, 3);
    vm::VM vm;
    BlockState block_state{db, vm};
    replace_contract(block_state, 0);

    State speculative{block_state};
    EXPECT_EQ(speculative.get_nonce(CONTRACT), 1);
    EXPECT_EQ(speculative.get_storage(CONTRACT, INPUT_SLOT), bytes32_t{});
    replace_contract(block_state, 7);
    replace_contract(block_state, 10);
    EXPECT_FALSE(block_state.can_merge(speculative));
    EXPECT_EQ(block_state.read_storage(CONTRACT, INPUT_SLOT), bytes32_t{10});
    EXPECT_EQ(block_state.read_storage(CONTRACT, OUTPUT_SLOT), bytes32_t{});
}

template <class Trait>
class LegacySpeculationExecutionTest : public ::testing::Test
{
};

using LegacyTraits = ::testing::Types<
    EvmTraits<MONAD_ETH_BERLIN>, EvmTraits<MONAD_ETH_LONDON>,
    EvmTraits<MONAD_ETH_SHANGHAI>>;
TYPED_TEST_SUITE(LegacySpeculationExecutionTest, LegacyTraits);

TYPED_TEST(
    LegacySpeculationExecutionTest,
    executes_before_predecessor_and_retries_storage_reset)
{
    // Copy slot 0 to slot 1. A stale speculative execution copies 3; its retry
    // must copy the replacement's 7 and charge the same gas as serial
    // execution.
    auto const code = 0x60005460015500_bytes;
    std::atomic<bool> storage_read{false};
    mpt::Db raw_db{std::make_unique<InMemoryMachine>()};
    TrieDb source_db{raw_db};
    ObservedDb db{source_db, [&] { storage_read.store(true); }};
    seed_contract(db, 3, code);
    vm::VM vm;
    BlockState block_state{db, vm};
    BlockMetrics metrics;
    Transaction const tx{
        .sc =
            {.signature =
                 {.r =
                      0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                  .s =
                      0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256}},
        .gas_limit = 200'000,
        .to = CONTRACT};
    BlockHeader const header{.number = 1, .gas_limit = 1'000'000};
    BlockHashBufferFinalized const block_hash_buffer;
    EthereumMainnet const chain;
    auto const chain_context = ChainContext<TypeParam>::debug_empty();
    NoopCallTracer call_tracer;
    trace::StateTracer state_tracer = std::monostate{};
    boost::fibers::promise<void> predecessor;
    boost::fibers::promise<Result<Receipt>> completion;
    auto completed = completion.get_future();
    boost::fibers::fiber execution{
        boost::fibers::launch::dispatch, [&] {
            try {
                completion.set_value(ExecuteTransaction<TypeParam>{
                    chain,
                    1,
                    tx,
                    SENDER,
                    {},
                    header,
                    block_hash_buffer,
                    block_state,
                    metrics,
                    predecessor,
                    call_tracer,
                    state_tracer,
                    chain_context,
                    nullptr}());
            }
            catch (...) {
                completion.set_exception(std::current_exception());
            }
        }};

    auto const deadline =
        std::chrono::steady_clock::now() + std::chrono::seconds{10};
    while (!storage_read.load() &&
           std::chrono::steady_clock::now() < deadline) {
        boost::this_fiber::yield();
    }
    EXPECT_TRUE(storage_read.load());
    replace_contract(block_state, 7, code);
    predecessor.set_value();
    auto result = completed.get();
    execution.join();
    ASSERT_FALSE(result.has_error());
    EXPECT_EQ(result.value().status, 1);
    EXPECT_EQ(metrics.num_retries, 1);
    EXPECT_EQ(block_state.read_storage(CONTRACT, OUTPUT_SLOT), bytes32_t{7});

    mpt::Db serial_raw_db{std::make_unique<InMemoryMachine>()};
    TrieDb serial_db{serial_raw_db};
    seed_contract(serial_db, 7, code);
    BlockState serial_state{serial_db, vm};
    BlockMetrics serial_metrics;
    NoopCallTracer serial_call_tracer;
    trace::StateTracer serial_state_tracer = std::monostate{};
    boost::fibers::promise<void> serial_predecessor;
    serial_predecessor.set_value();
    auto serial_result = ExecuteTransaction<TypeParam>{
        chain,
        1,
        tx,
        SENDER,
        {},
        header,
        block_hash_buffer,
        serial_state,
        serial_metrics,
        serial_predecessor,
        serial_call_tracer,
        serial_state_tracer,
        chain_context,
        nullptr}();
    ASSERT_FALSE(serial_result.has_error());
    EXPECT_EQ(result.value(), serial_result.value());
    EXPECT_EQ(serial_metrics.num_retries, 0);

    auto [deltas, codes, reads] = std::move(block_state).release();
    commit_sequential(db, *deltas, codes, header);
    auto [serial_deltas, serial_codes, serial_reads] =
        std::move(serial_state).release();
    commit_sequential(serial_db, *serial_deltas, serial_codes, header);
    EXPECT_EQ(db.state_root(), serial_db.state_root());
}

MONAD_TEST_NAMESPACE_END
