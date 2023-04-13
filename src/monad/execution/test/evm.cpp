#include <monad/execution/config.hpp>
#include <monad/execution/evm.hpp>

#include <monad/execution/test/fakes.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using evm_t = Evm<fake::State, fake::traits::alpha<fake::State>>;

TEST(Evm, make_account_address)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[to].nonce = 0;

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::make_account_address(s, m);

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, to);
    EXPECT_EQ(s._map[from].balance, 9'930'000'000);
    EXPECT_EQ(s._map[from].nonce, 6);
    EXPECT_EQ(s._map[to].balance, 70'000'000);
    EXPECT_EQ(s._map[to].nonce, 1);
}

TEST(Evm, make_account_address_create2)
{
    constexpr static auto from{
        0x00000000000000000000000000000000deadbeef_address};
    constexpr static auto new_address{
        0x60f3f640a8508fC6a86d45DF051962668E1e8AC7_address};
    static constexpr auto cafebabe_salt{
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32};
    static const uint8_t deadbeef[4]{0xde, 0xad, 0xbe, 0xef};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[new_address].nonce = 0;

    evmc_message m{
        .kind = EVMC_CREATE2,
        .gas = 20'000,
        .sender = from,
        .input_data = &deadbeef[0],
        .input_size = 4,
        .create2_salt = cafebabe_salt,
    };
    uint256_t v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::make_account_address(s, m);

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, new_address);
    EXPECT_EQ(s._map[from].balance, 9'930'000'000);
    EXPECT_EQ(s._map[from].nonce, 6);
    EXPECT_EQ(s._map[new_address].balance, 70'000'000);
    EXPECT_EQ(s._map[new_address].nonce, 1);
}

TEST(Evm, create_with_insufficient)
{
    constexpr static auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t v{70'000'000'000'000'000}; // too much
    intx::be::store(m.value.bytes, v);

    auto const unexpected = evm_t::make_account_address(s, m);

    auto const result = unexpected.error();
    EXPECT_EQ(result.status_code, EVMC_INSUFFICIENT_BALANCE);
}

TEST(Evm, create_nonce_out_of_range)
{
    constexpr static auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = std::numeric_limits<uint64_t>::max();

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const unexpected = evm_t::make_account_address(s, m);

    auto const result = unexpected.error();
    EXPECT_EQ(result.status_code, EVMC_ARGUMENT_OUT_OF_RANGE);
}

TEST(Evm, eip684_existing_nonce)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[to].nonce = 5; // existing

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const unexpected = evm_t::make_account_address(s, m);

    auto const result = unexpected.error();
    EXPECT_EQ(result.status_code, EVMC_INVALID_INSTRUCTION);
}

TEST(Evm, eip684_existing_code)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    constexpr static auto code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[to].code_hash = code_hash; // existing

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const unexpected = evm_t::make_account_address(s, m);

    auto const result = unexpected.error();
    EXPECT_EQ(result.status_code, EVMC_INVALID_INSTRUCTION);
}

TEST(Evm, transfer_call_balances)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[to].balance = 0;

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 20'000,
        .recipient = to,
        .sender = from,
    };
    uint256_t v{7'000'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::transfer_call_balances(s, m);

    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(s._map[from].balance, 3'000'000'000);
    EXPECT_EQ(s._map[to].balance, 7'000'000'000);
}

TEST(Evm, dont_transfer_on_delegatecall)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[to].balance = 0;

    evmc_message m{
        .kind = EVMC_DELEGATECALL,
        .gas = 20'000,
        .recipient = to,
        .sender = from,
    };
    uint256_t v{7'000'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::transfer_call_balances(s, m);

    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(s._map[from].balance, 10'000'000'000);
    EXPECT_EQ(s._map[to].balance, 0);
}

TEST(Evm, dont_transfer_on_staticcall)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;
    s._map[to].balance = 0;

    evmc_message m{
        .kind = EVMC_CALL,
        .flags = EVMC_STATIC,
        .gas = 20'000,
        .recipient = to,
        .sender = from,
    };
    uint256_t v{7'000'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::transfer_call_balances(s, m);

    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(s._map[from].balance, 10'000'000'000);
    EXPECT_EQ(s._map[to].balance, 0);
}
