#include <monad/config.hpp>
#include <monad/core/concepts.hpp>

#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;

using state_t = execution::fake::State;

static_assert(concepts::fork_traits<fork_traits::frontier, state_t>);
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

    execution::fake::State s{};
    s._selfdestructs = 10;

    EXPECT_EQ(f.get_selfdestruct_refund(s), 240'000);
    EXPECT_EQ(f.max_refund_quotient(), 2);

    s._touched_dead = 10;
    f.destruct_touched_dead(s);
    EXPECT_EQ(s._touched_dead, 10);

    uint8_t const ptr[5]{0x00};
    auto const a{0xbebebebebebebebebebebebebebebebebebebebe_address};
    auto const null{0x0000000000000000000000000000000000000000_address};
    evmc::Result r{EVMC_SUCCESS, 11'000, 0, ptr, 5};

    EXPECT_EQ(f.store_contract_code(s, a, r), true);
    EXPECT_EQ(r.gas_left, 10'000);
    EXPECT_EQ(r.create_address, a);

    r.gas_left = 999;
    r.create_address = null;
    EXPECT_EQ(f.store_contract_code(s, a, r), true);
    EXPECT_EQ(r.gas_left, 999);
    EXPECT_EQ(r.create_address, null);

    r.status_code = EVMC_INVALID_MEMORY_ACCESS;
    r.create_address = null;
    r.gas_left = 11'000;
    EXPECT_EQ(f.store_contract_code(s, a, r), true);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);
}

static_assert(concepts::fork_traits<fork_traits::homestead, state_t>);
TEST(fork_traits, homestead)
{
    fork_traits::homestead h{};
    Transaction t{};
    EXPECT_EQ(h.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(h.intrinsic_gas(t), 21'000);
    EXPECT_EQ(h.starting_nonce(), 0);

    execution::fake::State s{};
    uint8_t const ptr[5]{0x00};
    auto const a{0xbebebebebebebebebebebebebebebebebebebebe_address};
    auto const null{0x0000000000000000000000000000000000000000_address};
    evmc::Result r{EVMC_SUCCESS, 11'000, 0, ptr, 5};

    EXPECT_EQ(h.store_contract_code(s, a, r), true);
    EXPECT_EQ(r.gas_left, 10'000);
    EXPECT_EQ(r.create_address, a);

    r.gas_left = 999;
    r.create_address = null;
    EXPECT_EQ(h.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.status_code, EVMC_OUT_OF_GAS);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);

    r.status_code = EVMC_INVALID_MEMORY_ACCESS;
    r.create_address = null;
    r.gas_left = 11'000;
    EXPECT_EQ(h.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);
}

static_assert(concepts::fork_traits<fork_traits::spurious_dragon, state_t>);
TEST(fork_traits, spurious_dragon)
{
    fork_traits::spurious_dragon sd{};
    Transaction t{};
    EXPECT_EQ(sd.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(sd.intrinsic_gas(t), 21'000);
    EXPECT_EQ(sd.starting_nonce(), 1);

    execution::fake::State s{};
    s._touched_dead = 10;
    sd.destruct_touched_dead(s);
    EXPECT_EQ(s._touched_dead, 0);

    uint8_t const ptr[25000]{0x00};
    auto const a{0xbebebebebebebebebebebebebebebebebebebebe_address};
    auto const null{0x0000000000000000000000000000000000000000_address};
    evmc::Result r{EVMC_SUCCESS, 11'000, 0, ptr, 25'000};

    EXPECT_EQ(sd.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.status_code, EVMC_OUT_OF_GAS);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);
}

static_assert(concepts::fork_traits<fork_traits::byzantium, state_t>);
TEST(fork_traits, byzantium)
{
    fork_traits::byzantium b{};
    Transaction t{};
    EXPECT_EQ(b.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(b.intrinsic_gas(t), 21'000);
    EXPECT_EQ(b.starting_nonce(), 1);

    execution::fake::State s{};
    s._touched_dead = 10;
    b.destruct_touched_dead(s);
    EXPECT_EQ(s._touched_dead, 0);

    uint8_t const ptr[25]{0x00};
    auto const a{0xbebebebebebebebebebebebebebebebebebebebe_address};
    auto const null{0x0000000000000000000000000000000000000000_address};
    evmc::Result r{EVMC_SUCCESS, 11'000, 0, ptr, 25};
    EXPECT_EQ(b.store_contract_code(s, a, r), true);
    EXPECT_EQ(r.status_code, EVMC_SUCCESS);
    EXPECT_EQ(r.gas_left, 6'000);
    EXPECT_EQ(r.create_address, a);

    r.gas_left = 999;
    r.create_address = null;
    EXPECT_EQ(b.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.status_code, EVMC_OUT_OF_GAS);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);

    r.status_code = EVMC_INVALID_MEMORY_ACCESS;
    r.gas_left = 11'000;
    EXPECT_EQ(b.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);

    r.status_code = EVMC_REVERT;
    r.gas_left = 11'000;
    EXPECT_EQ(b.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.status_code, EVMC_REVERT);
    EXPECT_EQ(r.gas_left, 11'000);
    EXPECT_EQ(r.create_address, null);
}

static_assert(concepts::fork_traits<fork_traits::istanbul, state_t>);
TEST(fork_traits, intanbul)
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

static_assert(concepts::fork_traits<fork_traits::berlin, state_t>);
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

static_assert(concepts::fork_traits<fork_traits::london, state_t>);
TEST(fork_traits, london)
{
    fork_traits::london l{};
    execution::fake::State s{};
    s._selfdestructs = 10;

    EXPECT_EQ(l.get_selfdestruct_refund(s), 0);
    EXPECT_EQ(l.max_refund_quotient(), 5);

    uint8_t const ptr[25]{0xef};
    auto const a{0xbebebebebebebebebebebebebebebebebebebebe_address};
    auto const null{0x0000000000000000000000000000000000000000_address};
    evmc::Result r{EVMC_UNDEFINED_INSTRUCTION, 11'000, 0, ptr, 25};

    EXPECT_EQ(l.store_contract_code(s, a, r), false);
    EXPECT_EQ(r.status_code, EVMC_CONTRACT_VALIDATION_FAILURE);
    EXPECT_EQ(r.gas_left, 0);
    EXPECT_EQ(r.create_address, null);
}
