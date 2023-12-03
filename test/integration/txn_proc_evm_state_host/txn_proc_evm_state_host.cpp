#include <monad/core/account.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <optional>

using namespace monad;

static constexpr auto from = 0x5353535353535353535353535353535353535353_address;
static constexpr auto to = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto a = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
static constexpr auto o = 0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5_address;

using account_store_db_t = db::InMemoryTrieDB;

TEST(TxnProcEvmInterpStateHost, account_transfer_miner_ommer_award)
{
    account_store_db_t db{};
    BlockState bs{db};
    State s{bs};

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000'000}}}}},
        Code{});

    BlockHeader const bh{.number = 2, .beneficiary = a, .base_fee_per_gas = 0};
    BlockHeader const ommer{.number = 1, .beneficiary = o};
    Transaction t{
        .nonce = 0,
        .max_fee_per_gas = 10,
        .gas_limit = 25'000,
        .value = 1'000'000,
        .to = to,
        .from = from,
        .type = TransactionType::eip155};
    Block const b{.header = bh, .transactions = {t}, .ommers = {ommer}};

    constexpr auto rev = EVMC_BYZANTIUM;

    BlockHashBuffer const block_hash_buffer;

    auto const result = execute<rev>(t, bh, block_hash_buffer, s);

    ASSERT_TRUE(!result.has_error());

    auto const &r = result.value();

    EXPECT_EQ(r.status, Receipt::Status::SUCCESS);
    EXPECT_EQ(r.gas_used, 21'000);
    EXPECT_EQ(t.type, TransactionType::eip155);
    EXPECT_EQ(s.get_balance(from), bytes32_t{8'790'000});
    EXPECT_EQ(s.get_balance(to), bytes32_t{1'000'000});

    auto const reward = calculate_txn_award<rev>(t, 0, r.gas_used);
    s.add_to_balance(bh.beneficiary, reward);

    EXPECT_TRUE(bs.can_merge(s.state_));
    bs.merge(s.state_);

    apply_block_reward<rev>(bs, b);

    State s2{bs};
    EXPECT_EQ(s2.get_balance(a), bytes32_t{3'093'750'000'000'420'000});
    EXPECT_EQ(s2.get_balance(o), bytes32_t{2'625'000'000'000'000'000});
}

TEST(TxnProcEvmInterpStateHost, out_of_gas_account_creation_failure)
{
    // Block 46'402, txn 0
    static constexpr auto creator =
        0xA1E4380A3B1f749673E270229993eE55F35663b4_address;
    static constexpr auto created =
        0x9a049f5d18c239efaa258af9f3e7002949a977a0_address;
    account_store_db_t db{};
    BlockState bs{db};
    State s{bs};

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

    byte_string const code = {
        0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x00, 0x80, 0x54, 0x60, 0x01,
        0x60, 0xa0, 0x60, 0x02, 0x0a, 0x03, 0x19, 0x16, 0x33, 0x17, 0x90,
        0x55, 0x60, 0x06, 0x80, 0x60, 0x23, 0x60, 0x00, 0x39, 0x60, 0x00,
        0xf3, 0x00, 0x60, 0x60, 0x60, 0x40, 0x52, 0x00};
    BlockHeader const bh{.number = 2, .beneficiary = a, .base_fee_per_gas = 0};
    Transaction t{
        .nonce = 3,
        .max_fee_per_gas = 10'000'000'000'000, // 10'000 GWei
        .gas_limit = 24'000,
        .value = 0,
        .from = creator,
        .data = code,
        .type = TransactionType::eip155};
    Block const b{.header = bh, .transactions = {t}};

    constexpr auto rev = EVMC_FRONTIER;

    BlockHashBuffer const block_hash_buffer;

    auto const result = execute<rev>(t, bh, block_hash_buffer, s);

    ASSERT_TRUE(!result.has_error());

    auto const &r = result.value();

    EXPECT_EQ(r.status, Receipt::Status::FAILED);
    EXPECT_EQ(r.gas_used, 24'000);
    EXPECT_EQ(t.type, TransactionType::eip155);
    EXPECT_EQ(s.get_balance(creator), bytes32_t{8'760'000'000'000'000'000});
    EXPECT_EQ(s.get_balance(created), bytes32_t{0});

    auto const reward = calculate_txn_award<rev>(t, 0, r.gas_used);
    s.add_to_balance(b.header.beneficiary, reward);

    EXPECT_TRUE(bs.can_merge(s.state_));
    bs.merge(s.state_);

    apply_block_reward<rev>(bs, b);

    State s2{bs};
    EXPECT_EQ(s2.get_balance(a), bytes32_t{5'480'000'000'000'000'000});
}

TEST(TxnProcEvmInterpStateHost, out_of_gas_account_creation_failure_with_value)
{
    // Block 48'512, txn 0
    static constexpr auto creator =
        0x3D0768da09CE77d25e2d998E6a7b6eD4b9116c2D_address;
    static constexpr auto created =
        0x4dae54c8645c47dd55782091eca145c7bff974bc_address;
    account_store_db_t db{};
    BlockState bs{db};
    State s{bs};

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

    byte_string const code = {0xde, 0xad, 0xbe, 0xef};
    BlockHeader const bh{
        .number = 48'512, .beneficiary = a, .base_fee_per_gas = 0};
    Transaction t{
        .nonce = 2,
        .max_fee_per_gas = 57'935'965'411,
        .gas_limit = 90'000,
        .value = 10'000'000'000'000'000, // 0.01 Eth
        .from = creator,
        .data = code,
        .type = TransactionType::eip155};
    Block const b{.header = bh, .transactions = {t}};

    constexpr auto rev = EVMC_FRONTIER;

    BlockHashBuffer const block_hash_buffer;

    auto const result = execute<rev>(t, bh, block_hash_buffer, s);

    ASSERT_TRUE(!result.has_error());

    auto const &r = result.value();

    EXPECT_EQ(r.status, Receipt::Status::FAILED);
    EXPECT_EQ(r.gas_used, 90'000);
    EXPECT_EQ(t.type, TransactionType::eip155);
    EXPECT_EQ(s.get_balance(creator), bytes32_t{4'936'905'359'437'569'240});
    EXPECT_EQ(s.get_nonce(creator), 3);
    EXPECT_FALSE(s.account_exists(created));

    auto const reward = calculate_txn_award<rev>(t, 0, r.gas_used);
    s.add_to_balance(bh.beneficiary, reward);

    EXPECT_TRUE(bs.can_merge(s.state_));
    bs.merge(s.state_);

    apply_block_reward<rev>(bs, b);

    State s2{bs};
    EXPECT_EQ(s2.get_balance(a), bytes32_t{5'010'428'473'773'980'000});
}
