#include <monad/db/block_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/block_state_ops.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <unordered_map>

using namespace monad;

static constexpr auto from = 0x5353535353535353535353535353535353535353_address;
static constexpr auto to = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto a = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
static constexpr auto o = 0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5_address;

using account_store_db_t = db::InMemoryTrieDB;

template <class TState, class TTraits>
using evm_t = execution::Evm<TState, TTraits>;

template <class TState, class TTraits>
using evm_host_t = execution::EvmcHost<TState, TTraits, evm_t<TState, TTraits>>;

using mutex_t = std::shared_mutex;

TEST(TxnProcEvmInterpStateHost, account_transfer_miner_ommer_award)
{
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    BlockState<mutex_t> bs;
    state::State s{bs, db, blocks};

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000'000}}}}},
        Code{});

    BlockHeader const bh{.number = 2, .beneficiary = a};
    BlockHeader const ommer{.number = 1, .beneficiary = o};
    Transaction const t{
        .nonce = 0,
        .max_fee_per_gas = 10,
        .gas_limit = 25'000,
        .amount = 1'000'000,
        .to = to,
        .from = from,
        .type = TransactionType::eip155};
    Block const b{.header = bh, .transactions = {t}, .ommers = {ommer}};

    using state_t = decltype(s);
    using fork_t = monad::fork_traits::byzantium;
    using tp_t = execution::TransactionProcessor<state_t, fork_t>;

    tp_t tp{};
    evm_host_t<state_t, fork_t> h{bh, t, s};

    EXPECT_EQ(
        tp.validate(s, t, std::nullopt), execution::TransactionStatus::SUCCESS);

    auto r = tp.execute(s, h, t, 0, bh.beneficiary);
    EXPECT_EQ(r.status, Receipt::Status::SUCCESS);
    EXPECT_EQ(r.gas_used, 21'000);
    EXPECT_EQ(t.type, TransactionType::eip155);
    EXPECT_EQ(s.get_balance(from), bytes32_t{8'790'000});
    EXPECT_EQ(s.get_balance(to), bytes32_t{1'000'000});

    fork_t::apply_block_award(
        bs,
        db,
        blocks,
        b,
        fork_t::calculate_txn_award(
            t, b.header.base_fee_per_gas.value_or(0), r.gas_used));

    EXPECT_TRUE(can_merge(bs.state, s.state_));
    merge(bs.state, s.state_);

    EXPECT_EQ(s.get_balance(a), bytes32_t{3'093'750'000'000'210'000});
    EXPECT_EQ(s.get_balance(o), bytes32_t{2'625'000'000'000'000'000});
}

TEST(TxnProcEvmInterpStateHost, out_of_gas_account_creation_failure)
{
    // Block 46'402, txn 0
    static constexpr auto creator =
        0xA1E4380A3B1f749673E270229993eE55F35663b4_address;
    static constexpr auto created =
        0x9a049f5d18c239efaa258af9f3e7002949a977a0_address;
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    BlockState<mutex_t> bs;
    state::State s{bs, db, blocks};

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{}}}},
            {creator,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 9'000'000'000'000'000'000, .nonce = 3}}}}},
        Code{});

    byte_string code = {0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x00, 0x80, 0x54,
                        0x60, 0x01, 0x60, 0xa0, 0x60, 0x02, 0x0a, 0x03, 0x19,
                        0x16, 0x33, 0x17, 0x90, 0x55, 0x60, 0x06, 0x80, 0x60,
                        0x23, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3, 0x00, 0x60,
                        0x60, 0x60, 0x40, 0x52, 0x00};
    BlockHeader const bh{.number = 2, .beneficiary = a};
    Transaction const t{
        .nonce = 3,
        .max_fee_per_gas = 10'000'000'000'000, // 10'000 GWei
        .gas_limit = 24'000,
        .amount = 0,
        .from = creator,
        .data = code,
        .type = TransactionType::eip155};
    Block const b{.header = bh, .transactions = {t}};

    using state_t = decltype(s);
    using fork_t = monad::fork_traits::frontier;
    using tp_t = execution::TransactionProcessor<state_t, fork_t>;

    tp_t tp{};
    evm_host_t<state_t, fork_t> h{bh, t, s};

    EXPECT_EQ(
        tp.validate(s, t, std::nullopt), execution::TransactionStatus::SUCCESS);

    auto r = tp.execute(s, h, t, 0, bh.beneficiary);
    EXPECT_EQ(r.status, Receipt::Status::FAILED);
    EXPECT_EQ(r.gas_used, 24'000);
    EXPECT_EQ(t.type, TransactionType::eip155);
    EXPECT_EQ(s.get_balance(creator), bytes32_t{8'760'000'000'000'000'000});
    EXPECT_EQ(s.get_balance(created), bytes32_t{0});

    fork_t::apply_block_award(
        bs,
        db,
        blocks,
        b,
        fork_t::calculate_txn_award(
            t, b.header.base_fee_per_gas.value_or(0), r.gas_used));

    EXPECT_TRUE(can_merge(bs.state, s.state_));
    merge(bs.state, s.state_);

    EXPECT_EQ(s.get_balance(a), bytes32_t{5'240'000'000'000'000'000});
}

TEST(TxnProcEvmInterpStateHost, out_of_gas_account_creation_failure_with_value)
{
    // Block 48'512, txn 0
    static constexpr auto creator =
        0x3D0768da09CE77d25e2d998E6a7b6eD4b9116c2D_address;
    static constexpr auto created =
        0x4dae54c8645c47dd55782091eca145c7bff974bc_address;
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    BlockState<mutex_t> bs;
    state::State s{bs, db, blocks};

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{}}}},
            {creator,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 4'942'119'596'324'559'240, .nonce = 2}}}}},
        Code{});

    byte_string code = {0xde, 0xad, 0xbe, 0xef};
    BlockHeader const bh{.number = 48'512, .beneficiary = a};
    Transaction const t{
        .nonce = 2,
        .max_fee_per_gas = 57'935'965'411,
        .gas_limit = 90'000,
        .amount = 10'000'000'000'000'000, // 0.01 Eth
        .from = creator,
        .data = code,
        .type = TransactionType::eip155};
    Block const b{.header = bh, .transactions = {t}};

    using state_t = decltype(s);
    using fork_t = monad::fork_traits::frontier;
    using tp_t = execution::TransactionProcessor<state_t, fork_t>;

    tp_t tp{};
    evm_host_t<state_t, fork_t> h{bh, t, s};

    EXPECT_EQ(
        tp.validate(s, t, std::nullopt), execution::TransactionStatus::SUCCESS);

    auto r = tp.execute(s, h, t, 0, bh.beneficiary);
    EXPECT_EQ(r.status, Receipt::Status::FAILED);
    EXPECT_EQ(r.gas_used, 90'000);
    EXPECT_EQ(t.type, TransactionType::eip155);
    EXPECT_EQ(s.get_balance(creator), bytes32_t{4'936'905'359'437'569'240});
    EXPECT_EQ(s.get_nonce(creator), 3);
    EXPECT_FALSE(s.account_exists(created));

    fork_t::apply_block_award(
        bs,
        db,
        blocks,
        b,
        fork_t::calculate_txn_award(
            t, b.header.base_fee_per_gas.value_or(0), r.gas_used));

    EXPECT_TRUE(can_merge(bs.state, s.state_));
    merge(bs.state, s.state_);

    EXPECT_EQ(s.get_balance(a), bytes32_t{5'005'214'236'886'990'000});
}
