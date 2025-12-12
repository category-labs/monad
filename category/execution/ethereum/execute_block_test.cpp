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

#include <category/core/byte_string.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/mpt/traverse_util.hpp>
#include <monad/test/traits_test.hpp>

#include <test_resource_data.h>

using namespace monad;
using namespace monad::test;

using db_t = TrieDb;

namespace
{
    using monad::literals::operator""_bytes;

    auto const STRESS_TEST_CODE =
        0x5b614e206080511015603f5760006000614e206000600173aaaf5374fce5edbc8e2a8697c15331677e6ebf0b610640f16000556001608051016080526000565b60805160015500_bytes;
    auto const STRESS_TEST_CODE_HASH = to_bytes(keccak256(STRESS_TEST_CODE));
    auto const STRESS_TEST_ICODE = vm::make_shared_intercode(STRESS_TEST_CODE);

    auto const REFUND_TEST_CODE =
        0x6000600155600060025560006003556000600455600060055500_bytes;
    auto const REFUND_TEST_CODE_HASH = to_bytes(keccak256(REFUND_TEST_CODE));
    auto const REFUND_TEST_ICODE = vm::make_shared_intercode(REFUND_TEST_CODE);

    ///////////////////////////////////////////
    // DB Getters
    ///////////////////////////////////////////
    std::vector<CallFrame> read_call_frame(
        mpt::Node::SharedPtr root, mpt::Db &db, uint64_t const block_number,
        uint64_t const txn_idx)
    {
        using namespace mpt;

        using KeyedChunk = std::pair<Nibbles, byte_string>;

        Nibbles const min = mpt::concat(
            FINALIZED_NIBBLE,
            CALL_FRAME_NIBBLE,
            NibblesView{serialize_as_big_endian<sizeof(uint32_t)>(txn_idx)});
        Nibbles const max = mpt::concat(
            FINALIZED_NIBBLE,
            CALL_FRAME_NIBBLE,
            NibblesView{
                serialize_as_big_endian<sizeof(uint32_t)>(txn_idx + 1)});

        std::vector<KeyedChunk> chunks;
        RangedGetMachine machine{
            min,
            max,
            [&chunks](NibblesView const path, byte_string_view const value) {
                chunks.emplace_back(path, value);
            }};
        db.traverse(root, machine, block_number);
        MONAD_ASSERT(!chunks.empty());

        std::sort(
            chunks.begin(),
            chunks.end(),
            [](KeyedChunk const &c, KeyedChunk const &c2) {
                return c.first < NibblesView{c2.first};
            });

        byte_string const call_frames_encoded = std::accumulate(
            std::make_move_iterator(chunks.begin()),
            std::make_move_iterator(chunks.end()),
            byte_string{},
            [](byte_string const acc, KeyedChunk const chunk) {
                return std::move(acc) + std::move(chunk.second);
            });

        byte_string_view view{call_frames_encoded};
        auto const call_frame = rlp::decode_call_frames(view);
        MONAD_ASSERT(!call_frame.has_error());
        MONAD_ASSERT(view.empty());
        return call_frame.value();
    }
}

// test referenced from
// https://github.com/ethereum/tests/blob/develop/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/Call50000.json
// has been modified to do 20'000 calls instead of 50'000, in order to fit
// within the 250'000'000 gas limit in all revisions
TYPED_TEST(TraitsTest, call_frames_stress_test)
{
    using intx::operator""_u256;
    using intx::operator""_u128;
    using monad::literals::operator""_bytes;

    static constexpr auto from{
        0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address};
    static constexpr auto to{
        0xbbbf5374fce5edbc8e2a8697c15331677e6ebf0b_address};
    static constexpr auto ca{
        0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};

    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xffffffffffffffffffffffffffffffff_u128,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x0fffffffffffff,
                          .code_hash = STRESS_TEST_CODE_HASH}}}},
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x1b58, .code_hash = NULL_HASH}}}}},
        Code{{STRESS_TEST_CODE_HASH, STRESS_TEST_ICODE}},
        BlockHeader{.number = 0});

    byte_string const block_rlp =
        0xf90283f90219a0d2472bbb9c83b0e7615b791409c2efaccd5cb7d923741bbc44783bf0d063f5b6a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d4934794b94f5374fce5edbc8e2a8697c15331677e6ebf0ba0644bb1009c2332d1532062fe9c28cae87169ccaab2624aa0cfb4f0a0e59ac3aaa0cc2a2a77bb0d7a07b12d7e1d13b9f5dfff4f4bc53052b126e318f8b27b7ab8f9a027408083641cf20cfde86cd87cd57bf10c741d7553352ca96118e31ab8ceb9ceb901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018433428f00840ee6b2808203e800a000000000000000000000000000000000000000000000000000000000000200008800000000000000000aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421f863f861800a840ee6b28094bbbf5374fce5edbc8e2a8697c15331677e6ebf0b0a801ba0462186579a4be0ad8a63224059a11693b4c0684b9939f6c2394d1fbe045275f2a059d73f99e037295a5f8c0e656acdb5c8b9acd28ec73c320c277df61f2e2d54f9c0c0_bytes;
    byte_string_view block_rlp_view{block_rlp};
    auto const block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }
    auto const recovered_authorities =
        recover_authorities(block.value().transactions, pool);
    std::vector<std::vector<CallFrame>> call_frames(
        block.value().transactions.size());
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
    for (size_t i = 0; i < block.value().transactions.size(); ++i) {
        call_tracers.emplace_back(std::make_unique<CallTracer>(
            block.value().transactions[i], call_frames[i]));
        state_tracers.emplace_back(
            std::make_unique<trace::StateTracer>(std::monostate{}));
    }

    ankerl::unordered_dense::segmented_set<Address> const
        empty_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }
    for (std::vector<std::optional<Address>> const &authorities :
         recovered_authorities) {
        for (std::optional<Address> const &authority : authorities) {
            if (authority.has_value()) {
                senders_and_authorities.insert(authority.value());
            }
        }
    }

    ChainContext<typename TestFixture::Trait> chain_ctx = [&] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            return ChainContext<typename TestFixture::Trait>{
                .grandparent_senders_and_authorities =
                    empty_senders_and_authorities,
                .parent_senders_and_authorities = empty_senders_and_authorities,
                .senders_and_authorities = senders_and_authorities,
                .senders = senders,
                .authorities = recovered_authorities,
            };
        }
        else {
            return ChainContext<typename TestFixture::Trait>{};
        }
    }();

    auto execute = [&](Chain const &chain) -> Result<std::vector<Receipt>> {
        return execute_block<typename TestFixture::Trait>(
            chain,
            block.value(),
            senders,
            recovered_authorities,
            bs,
            block_hash_buffer,
            pool.fiber_group(),
            metrics,
            call_tracers,
            state_tracers,
            chain_ctx);
    };

    auto const receipts = [&] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            return execute(MonadMainnet{});
        }
        else {
            return execute(EthereumMainnet{});
        }
    }();
    ASSERT_TRUE(!receipts.has_error());

    bs.log_debug();

    auto const &transactions = block.value().transactions;
    BlockHeader const header{.number = 1};
    bytes32_t const block_id{header.number};
    bs.commit(
        block_id,
        header,
        receipts.value(),
        call_frames,
        senders,
        transactions,
        {},
        {});
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_call_frames =
        read_call_frame(tdb.get_root(), db, tdb.get_block_number(), 0);

    EXPECT_EQ(actual_call_frames.size(), 20'001);
}

// This test is based on the test `TraitsTest.call_frames_stress_test`
TYPED_TEST(TraitsTest, assertion_exception)
{
    using intx::operator""_u256;
    using monad::literals::operator""_bytes;

    static constexpr auto from{
        0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address};
    static constexpr auto to{
        0xbbbf5374fce5edbc8e2a8697c15331677e6ebf0b_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};

    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = STRESS_TEST_CODE_HASH}}}}},
        Code{{STRESS_TEST_CODE_HASH, STRESS_TEST_ICODE}},
        BlockHeader{.number = 0});

    byte_string const block_rlp =
        0xf90283f90219a0d2472bbb9c83b0e7615b791409c2efaccd5cb7d923741bbc44783bf0d063f5b6a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d4934794b94f5374fce5edbc8e2a8697c15331677e6ebf0ba0644bb1009c2332d1532062fe9c28cae87169ccaab2624aa0cfb4f0a0e59ac3aaa0cc2a2a77bb0d7a07b12d7e1d13b9f5dfff4f4bc53052b126e318f8b27b7ab8f9a027408083641cf20cfde86cd87cd57bf10c741d7553352ca96118e31ab8ceb9ceb901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018433428f00840ee6b2808203e800a000000000000000000000000000000000000000000000000000000000000200008800000000000000000aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421f863f861800a840ee6b28094bbbf5374fce5edbc8e2a8697c15331677e6ebf0b0a801ba0462186579a4be0ad8a63224059a11693b4c0684b9939f6c2394d1fbe045275f2a059d73f99e037295a5f8c0e656acdb5c8b9acd28ec73c320c277df61f2e2d54f9c0c0_bytes;
    byte_string_view block_rlp_view{block_rlp};
    auto block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }
    auto const recovered_authorities =
        recover_authorities(block.value().transactions, pool);
    std::vector<std::vector<CallFrame>> call_frames(
        block.value().transactions.size());
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
    for (size_t i = 0; i < block.value().transactions.size(); ++i) {
        call_tracers.emplace_back(std::make_unique<CallTracer>(
            block.value().transactions[i], call_frames[i]));
        state_tracers.emplace_back(
            std::make_unique<trace::StateTracer>(std::monostate{}));
    }

    ankerl::unordered_dense::segmented_set<Address> const
        empty_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }
    for (std::vector<std::optional<Address>> const &authorities :
         recovered_authorities) {
        for (std::optional<Address> const &authority : authorities) {
            if (authority.has_value()) {
                senders_and_authorities.insert(authority.value());
            }
        }
    }

    ChainContext<typename TestFixture::Trait> chain_ctx = [&] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            return ChainContext<typename TestFixture::Trait>{
                .grandparent_senders_and_authorities =
                    empty_senders_and_authorities,
                .parent_senders_and_authorities = empty_senders_and_authorities,
                .senders_and_authorities = senders_and_authorities,
                .senders = senders,
                .authorities = recovered_authorities,
            };
        }
        else {
            return ChainContext<typename TestFixture::Trait>{};
        }
    }();

    auto execute = [&](Chain const &chain) {
        (void)execute_block<typename TestFixture::Trait>(
            chain,
            block.value(),
            senders,
            recovered_authorities,
            bs,
            block_hash_buffer,
            pool.fiber_group(),
            metrics,
            call_tracers,
            state_tracers,
            chain_ctx);
    };

    if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
        EXPECT_THROW({ execute(MonadMainnet{}); }, MonadException);
    }
    else {
        EXPECT_THROW({ execute(EthereumMainnet{}); }, MonadException);
    }
}

// test referenced from :
// https://github.com/ethereum/tests/blob/v10.0/BlockchainTests/GeneralStateTests/stRefundTest/refund50_1.json
TYPED_TEST(TraitsTest, call_frames_refund)
{
    using intx::operator""_u256;
    using monad::literals::operator""_bytes;

    static constexpr auto from{
        0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address};
    static constexpr auto to{
        0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba_address};
    static constexpr auto ca{
        0x095e7baea6a6c7c4c2dfeb977efac326af552d87_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};

    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x989680,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x0,
                          .code_hash = NULL_HASH,
                          .nonce = 0x01}}}},
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x1b58,
                          .code_hash = REFUND_TEST_CODE_HASH}},
                 .storage =
                     {{bytes32_t{0x01}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x02}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x03}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x04}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x05}, {bytes32_t{}, bytes32_t{0x01}}}}}}},
        Code{{REFUND_TEST_CODE_HASH, REFUND_TEST_ICODE}},
        BlockHeader{.number = 0});

    byte_string const block_rlp =
        0xf9025ff901f7a01e736f5755fc7023588f262b496b6cbc18aa9062d9c7a21b1c709f55ad66aad3a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347942adc25665018aa1fe0e6bc666dac8fc2697ff9baa096841c0823ec823fdb0b0b8ea019c8dd6691b9f335e0433d8cfe59146e8b884ca0f0f9b1e10ec75d9799e3a49da5baeeab089b431b0073fb05fa90035e830728b8a06c8ab36ec0629c97734e8ac823cdd8397de67efb76c7beb983be73dcd3c78141b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008302000001830f42408259e78203e800a00000000000000000000000000000000000000000000000000000000000000000880000000000000000f862f860800a830186a094095e7baea6a6c7c4c2dfeb977efac326af552d8780801ba0eac92a424c1599d71b1c116ad53800caa599233ea91907e639b7cb98fa0da3bba06be40f001771af85bfba5e6c4d579e038e6465af3f55e71b9490ab48fcfa5b1ec0_bytes;
    byte_string_view block_rlp_view{block_rlp};
    auto block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());
    EXPECT_EQ(block.value().header.number, 1);

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }
    auto const recovered_authorities =
        recover_authorities(block.value().transactions, pool);
    std::vector<std::vector<CallFrame>> call_frames(
        block.value().transactions.size());
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
    for (size_t i = 0; i < block.value().transactions.size(); ++i) {
        call_tracers.emplace_back(std::make_unique<CallTracer>(
            block.value().transactions[i], call_frames[i]));
        state_tracers.emplace_back(
            std::make_unique<trace::StateTracer>(std::monostate{}));
    }

    ankerl::unordered_dense::segmented_set<Address> const
        empty_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }
    for (std::vector<std::optional<Address>> const &authorities :
         recovered_authorities) {
        for (std::optional<Address> const &authority : authorities) {
            if (authority.has_value()) {
                senders_and_authorities.insert(authority.value());
            }
        }
    }

    ChainContext<typename TestFixture::Trait> chain_ctx = [&] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            return ChainContext<typename TestFixture::Trait>{
                .grandparent_senders_and_authorities =
                    empty_senders_and_authorities,
                .parent_senders_and_authorities = empty_senders_and_authorities,
                .senders_and_authorities = senders_and_authorities,
                .senders = senders,
                .authorities = recovered_authorities,
            };
        }
        else {
            return ChainContext<typename TestFixture::Trait>{};
        }
    }();

    auto execute = [&](Chain const &chain) -> Result<std::vector<Receipt>> {
        return execute_block<typename TestFixture::Trait>(
            chain,
            block.value(),
            senders,
            recovered_authorities,
            bs,
            block_hash_buffer,
            pool.fiber_group(),
            metrics,
            call_tracers,
            state_tracers,
            chain_ctx);
    };

    auto const receipts = [&] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            return execute(MonadMainnet{});
        }
        else {
            return execute(EthereumMainnet{});
        }
    }();
    ASSERT_TRUE(!receipts.has_error());

    bs.log_debug();

    auto const &transactions = block.value().transactions;
    BlockHeader const header = block.value().header;
    bytes32_t const block_id{header.number};
    bs.commit(
        block_id,
        header,
        receipts.value(),
        call_frames,
        senders,
        transactions,
        {},
        std::nullopt);
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_call_frames =
        read_call_frame(tdb.get_root(), db, tdb.get_block_number(), 0);

    ASSERT_EQ(actual_call_frames.size(), 1);

    static constexpr auto gas_used = [] {
        if constexpr (is_evm_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::evm_rev() <= EVMC_BERLIN) {
                // value from
                // https://github.com/ethereum/legacytests/blob/1f581b8ccdc4c63acf5f2c5c1b155c690c32a8eb/src/LegacyTests/Constantinople/BlockchainTestsFiller/GeneralStateTests/stRefundTest/refund50_1_d0g0v0Filler.json
                // pre.0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b.balance -
                // expect[0].0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b.balance
                return static_cast<uint64_t>(0x186a0 - 0x012cb9);
            }
            else {
                // value from
                // https://github.com/ethereum/execution-specs/blob/v2.18.0rc5.dev1/tests/eest/static/state_tests/stRefundTest/refund50_1Filler.json
                // (expect[0].result.<eoa:sender:0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b>.balance
                // -
                // pre.<eoa:sender:0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b>.balance)
                // / transaction.gasPrice
                return static_cast<uint64_t>((10'000'000 - 9'631'760) / 10);
            }
        }
        else {
            if constexpr (TestFixture::Trait::monad_rev() > MONAD_ZERO) {
                // full gas_limit is charged since >=MONAD_ONE
                return 0x186a0;
            }
            else {
                static_assert(TestFixture::Trait::evm_rev() > EVMC_BERLIN);
                // same cost as >EVMC_BERLIN
                return static_cast<uint64_t>((10'000'000 - 9'631'760) / 10);
            }
        }
    }();
    CallFrame expected{
        .type = CallType::CALL,
        .flags = 0,
        .from = from,
        .to = ca,
        .value = 0,
        .gas = 0x186a0,
        .gas_used = gas_used,
        .status = EVMC_SUCCESS,
        .depth = 0,
        .logs = std::vector<CallFrame::Log>{},
    };

    EXPECT_EQ(actual_call_frames[0], expected);
}
