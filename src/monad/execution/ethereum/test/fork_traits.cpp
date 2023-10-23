#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>

#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::fork_traits;
using namespace monad::execution;

using db_t = db::InMemoryTrieDB;
using mutex_t = std::shared_mutex;

using state_t = state::State<mutex_t>;

namespace
{
    constexpr auto individual = 100u;
    constexpr auto total = individual * 116u;
}

constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};
constexpr auto b{0x5353535353535353535353535353535353535353_address};
constexpr auto c{0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address};
constexpr auto null{0x0000000000000000000000000000000000000000_address};

TEST(fork_traits, frontier)
{
    fork_traits::frontier f{};
    Transaction t{};
    EXPECT_EQ(f.intrinsic_gas(t), 21'000);

    t.data.push_back(0x00);
    EXPECT_EQ(f.intrinsic_gas(t), 21'004);

    t.data.push_back(0xff);
    EXPECT_EQ(f.intrinsic_gas(t), 21'072);
    EXPECT_EQ(f.starting_nonce(), 0);

    db_t db;
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});
    {
        BlockState<mutex_t> bs;
        state_t s{bs, db};

        EXPECT_EQ(f.max_refund_quotient(), 2);

        f.destruct_touched_dead(s);
        EXPECT_TRUE(s.account_exists(a));

        byte_string const code{0x00, 0x00, 0x00, 0x00, 0x00};
        uint8_t const output_data[] = {0xde, 0xad, 0xbe, 0xef};
        { // Successfully deploy code
            int64_t gas = 10'000;

            evmc::Result r{
                EVMC_SUCCESS, gas, 0, output_data, sizeof(output_data)};
            auto const r2 = frontier::deploy_contract_code(s, a, std::move(r));
            EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
            EXPECT_EQ(r2.gas_left, gas - 800); // G_codedeposit * size(code)
            EXPECT_EQ(r2.create_address, a);
            EXPECT_EQ(
                s.get_code(a), byte_string(output_data, sizeof(output_data)));
        }

        { // Initilization code succeeds, but deployment of code failed
            evmc::Result r{
                EVMC_SUCCESS, 700, 0, output_data, sizeof(output_data)};
            auto const r2 = frontier::deploy_contract_code(s, a, std::move(r));
            EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
            EXPECT_EQ(r2.gas_left, r.gas_left);
            EXPECT_EQ(r2.create_address, a);
        }

        // gas price
        EXPECT_EQ(
            fork_traits::frontier::gas_price(
                Transaction{.max_fee_per_gas = 1'000}, 0u),
            1'000);

        // txn award
        EXPECT_EQ(
            fork_traits::frontier::calculate_txn_award(
                Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
            uint256_t{9'000'000'000'000'000'000});
    }
    {
        // block award
        BlockState<mutex_t> bs;
        state_t s{bs, db};
        Block block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        fork_traits::frontier::apply_block_award(bs, db, block);
        db.commit(s.bs_.state, s.bs_.code);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(a)),
            5'312'500'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(b)),
            4'375'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(c)),
            3'750'000'000'000'000'000);
    }
}

TEST(fork_traits, homestead)
{
    fork_traits::homestead h{};
    Transaction t{};
    EXPECT_EQ(h.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(h.intrinsic_gas(t), 21'000);
    EXPECT_EQ(h.starting_nonce(), 0);

    db_t db;
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});
    BlockState<mutex_t> bs;

    byte_string const code{0x00, 0x00, 0x00, 0x00, 0x00};
    uint8_t const output_data[] = {0xde, 0xad, 0xbe, 0xef};

    {
        // Successfully deploy code
        state_t s{bs, db};
        int64_t gas = 10'000;

        evmc::Result r{EVMC_SUCCESS, gas, 0, output_data, sizeof(output_data)};
        auto const r2 = homestead::deploy_contract_code(s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
        EXPECT_EQ(r2.create_address, a);
        EXPECT_EQ(r2.gas_left,
                  r.gas_left - 800); // G_codedeposit * size(code)
        EXPECT_EQ(s.get_code(a), byte_string(output_data, sizeof(output_data)));
    }

    {
        // Fail to deploy code - out of gas
        state_t s{bs, db};
        evmc::Result r{EVMC_SUCCESS, 700, 0, output_data, sizeof(output_data)};
        auto const r2 = homestead::deploy_contract_code(s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_OUT_OF_GAS);
        EXPECT_EQ(r2.gas_left, 700);
        EXPECT_EQ(r2.create_address, null);
    }
}

static_assert(std::derived_from<fork_traits::dao_fork, fork_traits::homestead>);
static_assert(
    std::same_as<
        fork_traits::dao_fork::next_fork_t, fork_traits::tangerine_whistle>);
TEST(fork_traits, dao)
{
    db_t db{};

    StateDeltas state_deltas{};

    for (auto const addr : dao::child_accounts) {
        Account a{.balance = individual};
        state_deltas.emplace(addr, StateDelta{.account = {std::nullopt, a}});
    }
    state_deltas.emplace(
        dao::withdraw_account,
        StateDelta{.account = {std::nullopt, Account{.balance = 0}}});

    db.commit(state_deltas, Code{});

    BlockState<mutex_t> bs;

    fork_traits::dao_fork::transfer_balance_dao(bs, db, dao::dao_block_number);

    state_t s{bs, db};
    for (auto const &addr : dao::child_accounts) {
        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(addr)), 0u);
    }
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(dao::withdraw_account)), total);
}

static_assert(
    std::derived_from<fork_traits::tangerine_whistle, fork_traits::dao_fork>);
static_assert(std::same_as<
              fork_traits::tangerine_whistle::next_fork_t,
              fork_traits::spurious_dragon>);
TEST(fork_traits, tangerine_whistle)
{
    EXPECT_EQ(fork_traits::tangerine_whistle::rev, EVMC_TANGERINE_WHISTLE);

    // Check that the tranfer does not do anything
    db_t db{};

    StateDeltas state_deltas{};
    for (auto const addr : dao::child_accounts) {
        Account a{.balance = individual};
        state_deltas.emplace(addr, StateDelta{.account = {std::nullopt, a}});
    }
    state_deltas.emplace(
        dao::withdraw_account,
        StateDelta{.account = {std::nullopt, Account{.balance = 0}}});

    db.commit(state_deltas, Code{});

    BlockState<mutex_t> bs;

    fork_traits::tangerine_whistle::transfer_balance_dao(
        bs, db, fork_traits::tangerine_whistle::last_block_number);

    state_t s{bs, db};

    for (auto const &addr : dao::child_accounts) {
        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(addr)), individual);
    }
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(dao::withdraw_account)), 0u);
}

TEST(fork_traits, spurious_dragon)
{
    fork_traits::spurious_dragon sd{};
    Transaction t{};
    EXPECT_EQ(sd.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(sd.intrinsic_gas(t), 21'000);
    EXPECT_EQ(sd.starting_nonce(), 1);

    db_t db;
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    BlockState<mutex_t> bs;
    state_t s{bs, db};
    s.add_to_balance(a, 0);
    sd.destruct_touched_dead(s);

    EXPECT_FALSE(s.account_exists(a));

    uint8_t const ptr[25000]{0x00};
    byte_string code{ptr, 25000};
    { // EIP-170 Code too big to deploy
        evmc::Result r{
            EVMC_SUCCESS,
            std::numeric_limits<int64_t>::max(),
            0,
            code.data(),
            code.size()};
        auto const r2 =
            spurious_dragon::deploy_contract_code(s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_OUT_OF_GAS);
        EXPECT_EQ(r2.gas_left, 0);
        EXPECT_EQ(r2.create_address, null);
    }
}

TEST(fork_traits, byzantium)
{
    fork_traits::byzantium byz{};
    Transaction t{};
    EXPECT_EQ(byz.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(byz.intrinsic_gas(t), 21'000);
    EXPECT_EQ(byz.starting_nonce(), 1);

    db_t db;
    BlockState<mutex_t> bs;
    state_t as{bs, db};
    (void)as.get_balance(a);
    byz.destruct_touched_dead(as);

    EXPECT_FALSE(as.account_exists(a));

    // block award
    Block block{
        .header = {.number = 10, .beneficiary = a},
        .transactions = {},
        .ommers = {
            BlockHeader{.number = 9, .beneficiary = b},
            BlockHeader{.number = 8, .beneficiary = c}}};
    fork_traits::byzantium::apply_block_award(bs, db, block);
    state_t cs{bs, db};
    EXPECT_EQ(
        intx::be::load<uint256_t>(cs.get_balance(a)),
        3'187'500'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(cs.get_balance(b)),
        2'625'000'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(cs.get_balance(c)),
        2'250'000'000'000'000'000);
}

static_assert(
    std::derived_from<
        fork_traits::constantinople_and_petersburg, fork_traits::byzantium>);
static_assert(std::same_as<
              fork_traits::constantinople_and_petersburg::next_fork_t,
              fork_traits::istanbul>);
TEST(fork_traits, constantinople_and_petersburg)
{
    // block award
    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};

    Block block{
        .header = {.number = 10, .beneficiary = a},
        .transactions = {},
        .ommers = {
            BlockHeader{.number = 9, .beneficiary = b},
            BlockHeader{.number = 8, .beneficiary = c}}};
    fork_traits::constantinople_and_petersburg::apply_block_award(
        bs, db, block);

    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(a)), 2'125'000'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(b)), 1'750'000'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(c)), 1'500'000'000'000'000'000);
}

static_assert(
    std::derived_from<
        fork_traits::istanbul, fork_traits::constantinople_and_petersburg>);
static_assert(
    std::same_as<fork_traits::istanbul::next_fork_t, fork_traits::berlin>);
TEST(fork_traits, istanbul)
{
    fork_traits::istanbul i{};
    Transaction t{};
    EXPECT_EQ(i.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    t.data.push_back(0x00);
    EXPECT_EQ(i.intrinsic_gas(t), 21'004);

    t.data.push_back(0xff);
    EXPECT_EQ(i.intrinsic_gas(t), 21'020);
}

TEST(fork_traits, berlin)
{
    fork_traits::berlin b{};
    Transaction t{};
    EXPECT_EQ(b.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(b.intrinsic_gas(t), 21'000);

    static constexpr auto key1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr auto key2{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    t.access_list.push_back({*t.to, {key1, key2}});
    EXPECT_EQ(b.intrinsic_gas(t), 21'000 + 2400 + 1900 + 1900);

    t.data.push_back(0x00);
    t.data.push_back(0xff);
    EXPECT_EQ(b.intrinsic_gas(t), 27'220);
}

TEST(fork_traits, london)
{
    fork_traits::london l{};
    db_t db;
    BlockState<mutex_t> bs;
    state_t s{bs, db};

    EXPECT_EQ(l.max_refund_quotient(), 5);

    byte_string const illegal_code{0xef, 0x60};
    byte_string const code{0x00, 0x00, 0x00, 0x00, 0x00};
    uint8_t const output_data[] = {0xde, 0xad, 0xbe, 0xef};
    { // Successfully deploy code
        evmc::Result r{
            EVMC_SUCCESS, 5'000, 0, output_data, sizeof(output_data)};
        auto const r2 = london::deploy_contract_code(s, a, std::move(r));
        EXPECT_EQ(r2.create_address, a);
        EXPECT_EQ(r2.gas_left, r.gas_left - 800); // G_codedeposit * size(code)
    }

    { // Fail to deploy illegal code
        evmc::Result r{
            EVMC_SUCCESS, 1'000, 0, illegal_code.data(), illegal_code.size()};
        auto const r2 = london::deploy_contract_code(s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_CONTRACT_VALIDATION_FAILURE);
        EXPECT_EQ(r2.gas_left, 0);
        EXPECT_EQ(r2.create_address, null);
    }

    // gas price
    Transaction t1{
        .max_fee_per_gas = 3'000,
        .type = TransactionType::eip155,
        .max_priority_fee_per_gas = 1'000};
    Transaction t2{.max_fee_per_gas = 3'000, .type = TransactionType::eip155};
    Transaction t3{
        .max_fee_per_gas = 5'000,
        .type = TransactionType::eip1559,
        .max_priority_fee_per_gas = 1'000};
    Transaction t4{.max_fee_per_gas = 5'000, .type = TransactionType::eip1559};
    Transaction t5{
        .max_fee_per_gas = 5'000,
        .type = TransactionType::eip1559,
        .max_priority_fee_per_gas = 4'000};
    EXPECT_EQ(fork_traits::london::gas_price(t1, 2'000u), 3'000);
    EXPECT_EQ(fork_traits::london::gas_price(t2, 2'000u), 3'000);
    EXPECT_EQ(fork_traits::london::gas_price(t3, 2'000u), 3'000);
    EXPECT_EQ(fork_traits::london::gas_price(t4, 2'000u), 2'000);
    EXPECT_EQ(fork_traits::london::gas_price(t5, 2'000u), 5'000);

    // txn award
    EXPECT_EQ(
        fork_traits::london::calculate_txn_award(
            Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
        uint256_t{9'000'000'000'000'000'000});
}

// EIP-3675
TEST(fork_traits, paris_apply_block_reward)
{
    Block block{};
    block.header.beneficiary = a;
    db_t db{};
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}}},
        Code{});

    {
        db_t db;
        BlockState<mutex_t> bs;
        state_t s{bs, db};

        fork_traits::paris::apply_block_award(bs, db, block);

        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(a)), 0u);
    }
    {
        db_t db;
        BlockState<mutex_t> bs;
        state_t s{bs, db};

        fork_traits::london::apply_block_award(bs, db, block);

        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(a)),
            fork_traits::constantinople_and_petersburg::block_reward);
    }
}

// EIP-3651
TEST(fork_traits, shanghai_warm_coinbase)
{
    db_t db{};

    {
        db_t db;
        BlockState<mutex_t> bs;
        state_t s{bs, db};

        fork_traits::shanghai::warm_coinbase(s, a);

        EXPECT_EQ(s.access_account(a), EVMC_ACCESS_WARM);
    }
    {
        db_t db;
        BlockState<mutex_t> bs;
        state_t s{bs, db};

        fork_traits::london::warm_coinbase(s, a);

        EXPECT_EQ(s.access_account(a), EVMC_ACCESS_COLD);
    }
}

// EIP-3860
TEST(fork_traits, shanghai_contract_creation_cost_exceed_limit)
{
    byte_string long_data;
    for (auto i = 0u; i < uint64_t{0xc002}; ++i) {
        long_data += {0xc0};
    }
    // exceed EIP-3860 limit
    Transaction t{.data = long_data};

    EXPECT_FALSE(fork_traits::shanghai::init_code_valid(t));
}

// EIP-3860
TEST(fork_traits, shanghai_contract_creation_cost)
{
    byte_string data;
    for (auto i = 0u; i < uint64_t{0x80}; ++i) {
        data += {0xc0};
    }

    Transaction t{.data = data};

    EXPECT_TRUE(fork_traits::shanghai::init_code_valid(t));
    EXPECT_EQ(
        fork_traits::shanghai::intrinsic_gas(t),
        32'000u + 21'000u + 16u * 128u + 0u + 4u * 2u);
}

// EIP-4895
TEST(fork_traits, shanghai_withdrawal)
{
    std::optional<std::vector<Withdrawal>> withdrawals{};
    Withdrawal w1 = {
        .index = 0, .validator_index = 0, .amount = 100u, .recipient = a};
    Withdrawal w2 = {
        .index = 1, .validator_index = 0, .amount = 300u, .recipient = a};
    Withdrawal w3 = {
        .index = 2, .validator_index = 0, .amount = 200u, .recipient = b};
    withdrawals = {w1, w2, w3};

    db_t db{};
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}},
            {b, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}}},
        Code{});

    BlockState<mutex_t> bs;

    state_t state{bs, db};
    fork_traits::shanghai::process_withdrawal(state, withdrawals);

    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(a)),
        uint256_t{400u} * uint256_t{1'000'000'000u});
    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(b)),
        uint256_t{200u} * uint256_t{1'000'000'000u});
}
