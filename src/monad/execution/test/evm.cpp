#include <monad/core/concepts.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/evm.hpp>

#include <monad/execution/test/fakes.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using traits_t = fake::traits::alpha<fake::State>;

template <concepts::fork_traits<fake::State> TTraits>
using traits_templated_static_precompiles_t = StaticPrecompiles<
    fake::State, TTraits, typename TTraits::static_precompiles_t>;

template <concepts::fork_traits<fake::State> TTraits>
using traits_templated_evm_t =
    Evm<fake::State, fake::traits::alpha<fake::State>,
        traits_templated_static_precompiles_t<TTraits>, fake::Interpreter>;

using evm_t = traits_templated_evm_t<traits_t>;
using evm_host_t = fake::EvmHost<
    fake::State, traits_t,
    fake::Evm<
        fake::State, traits_t, fake::static_precompiles::OneHundredGas,
        fake::Interpreter>>;

TEST(Evm, make_account_address)
{
    constexpr static auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    constexpr static auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State s{};
    s._map[from].balance = 10'000'000'000;
    s._map[from].nonce = 5;

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

TEST(Evm, create_contract_account)
{
    constexpr static auto from{
        0x5353535353535353535353535353535353535353_address};
    constexpr static auto new_addr{
        0x58f3f9ebd5dbdf751f12d747b02d00324837077d_address};
    constexpr static auto new_addr2{
        0x312c420ec31bc2760e2556911ccf7e5c7162909f_address};
    fake::State s{};
    evm_host_t h{};
    s._map.emplace(from, Account{.balance = 50'000u});
    traits_t::_gas_creation_cost = 5'000;
    traits_t::_success_store_contract = true;
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_SUCCESS, .gas_left = 8'000}};

    evmc_message m{.kind = EVMC_CREATE, .gas = 12'000, .sender = from};

    auto const result = evm_t::create_contract_account(&h, s, m);

    EXPECT_EQ(result.create_address, new_addr);
    EXPECT_EQ(result.gas_left, 3'000);

    m.kind = EVMC_CREATE2;

    auto const result2 = evm_t::create_contract_account(&h, s, m);

    EXPECT_EQ(result2.create_address, new_addr2);
    EXPECT_EQ(result2.gas_left, 3'000);
}

TEST(Evm, revert_create_account)
{
    constexpr static auto from{
        0x5353535353535353535353535353535353535353_address};
    constexpr static auto null{
        0x0000000000000000000000000000000000000000_address};
    fake::State s{};
    evm_host_t h{};
    s._map.emplace(from, Account{.balance = 10'000});
    traits_t::_gas_creation_cost = 10'000;
    traits_t::_success_store_contract = false;
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_REVERT, .gas_left = 11'000}};

    evmc_message m{.kind = EVMC_CREATE, .gas = 12'000, .sender = from};

    auto const result = evm_t::create_contract_account(&h, s, m);

    EXPECT_TRUE(s._map.empty()); // revert was called on the fake
    EXPECT_EQ(result.create_address, null);
    EXPECT_EQ(result.gas_left, 1'000);
}

TEST(Evm, call_evm)
{
    constexpr static auto from{
        0x5353535353535353535353535353535353535353_address};
    constexpr static auto to{
        0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8_address};
    fake::State s{};
    evm_host_t h{};
    s._map.emplace(from, Account{.balance = 50'000u});
    s._map.emplace(to, Account{.balance = 50'000u});
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_SUCCESS, .gas_left = 7'000}};

    evmc_message m{
        .kind = EVMC_CALL, .gas = 12'000, .recipient = to, .sender = from};
    uint256_t v{6'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::call_evm(&h, s, m);

    EXPECT_EQ(s._map[from].balance, 44'000);
    EXPECT_EQ(s._map[to].balance, 56'000);
    EXPECT_EQ(result.gas_left, 7'000);
}

TEST(Evm, static_precompile_execution)
{
    using beta_traits_t = fake::traits::beta<fake::State>;
    using alpha_evm_t = evm_t;
    using beta_evm_t = traits_templated_evm_t<beta_traits_t>;

    constexpr static auto from{
        0x5353535353535353535353535353535353535353_address};
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000001_address};
    fake::State s{};
    evm_host_t h{};
    s._map.emplace(from, Account{.balance = 15'000});
    s._map.emplace(code_address, Account{.nonce = 4});

    constexpr static char data[] = "hello world";
    constexpr static auto data_size = sizeof(data);

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 400,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<const unsigned char *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address};

    auto const alpha_result = alpha_evm_t::call_evm(&h, s, m);
    auto const beta_result = beta_evm_t::call_evm(&h, s, m);

    EXPECT_EQ(alpha_result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(alpha_result.gas_left, 280);
    EXPECT_EQ(alpha_result.output_size, data_size);
    EXPECT_EQ(
        std::memcmp(alpha_result.output_data, m.input_data, data_size), 0);
    EXPECT_NE(alpha_result.output_data, m.input_data);

    EXPECT_EQ(beta_result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(beta_result.gas_left, 220);
    EXPECT_EQ(beta_result.output_size, data_size);
    EXPECT_EQ(std::memcmp(beta_result.output_data, m.input_data, data_size), 0);
    EXPECT_NE(beta_result.output_data, m.input_data);
}

TEST(Evm, out_of_gas_static_precompile_execution)
{
    constexpr static auto from{
        0x5353535353535353535353535353535353535353_address};
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000001_address};
    fake::State s{};
    evm_host_t h{};
    s._map.emplace(from, Account{.balance = 15'000});
    s._map.emplace(code_address, Account{.nonce = 6});

    constexpr static char data[] = "hello world";
    constexpr static auto data_size = sizeof(data);

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 100,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<const unsigned char *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address};

    evmc::Result const result = evm_t::call_evm(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_OUT_OF_GAS);
}

TEST(Evm, revert_call_evm)
{
    constexpr static auto from{
        0x5353535353535353535353535353535353535353_address};
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000003_address};
    fake::State s{};
    evm_host_t h{};
    s._map.emplace(from, Account{.balance = 15'000});
    s._map.emplace(code_address, Account{.nonce = 10});
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_REVERT, .gas_left = 6'000}};

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 12'000,
        .recipient = code_address,
        .sender = from,
        .code_address = code_address};

    auto const result = evm_t::call_evm(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_REVERT);
    EXPECT_TRUE(s._map.empty()); // revert was called on the fake
    EXPECT_EQ(result.gas_left, 6'000);
}
