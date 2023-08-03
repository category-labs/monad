#include <monad/core/concepts.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/evm.hpp>

#include <monad/execution/test/fakes.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

static constexpr auto null{0x0000000000000000000000000000000000000000_address};

using traits_t = fake::traits::alpha<fake::State::ChangeSet>;

template <concepts::fork_traits<fake::State::ChangeSet> TTraits>
using traits_templated_static_precompiles_t = StaticPrecompiles<
    fake::State::ChangeSet, TTraits, typename TTraits::static_precompiles_t>;

template <concepts::fork_traits<fake::State::ChangeSet> TTraits>
using traits_templated_evm_t =
    Evm<fake::State::ChangeSet, fake::traits::alpha<fake::State::ChangeSet>,
        traits_templated_static_precompiles_t<TTraits>, fake::Interpreter>;

using evm_t = traits_templated_evm_t<traits_t>;
using evm_host_t = fake::EvmHost<
    fake::State::ChangeSet, traits_t,
    fake::Evm<
        fake::State::ChangeSet, traits_t,
        fake::static_precompiles::OneHundredGas, fake::Interpreter>>;

TEST(Evm, make_account_address)
{
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 6;

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
    EXPECT_EQ(s._accounts[from].nonce, 7);
    EXPECT_EQ(s._accounts[to].nonce, 1);
}

TEST(Evm, make_account_address_create2)
{
    static constexpr auto from{
        0x00000000000000000000000000000000deadbeef_address};
    static constexpr auto new_address{
        0x60f3f640a8508fC6a86d45DF051962668E1e8AC7_address};
    static constexpr auto cafebabe_salt{
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32};
    static const uint8_t deadbeef[4]{0xde, 0xad, 0xbe, 0xef};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 5;

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
    EXPECT_EQ(s._accounts[from].nonce, 6);
    EXPECT_EQ(s._accounts[new_address].nonce, 1);
}

TEST(Evm, create_with_insufficient)
{
    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;

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
    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = std::numeric_limits<uint64_t>::max();

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
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 6;
    s._accounts[to].nonce = 5; // existing

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
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static constexpr auto code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 6;
    s._accounts[to].code_hash = code_hash; // existing

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
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 6;
    s._accounts[to].balance = 0;

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
    EXPECT_EQ(s._accounts[from].balance, 3'000'000'000);
    EXPECT_EQ(s._accounts[to].balance, 7'000'000'000);
}

TEST(Evm, transfer_call_balances_to_self)
{
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to = from;
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 6;

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
    EXPECT_EQ(s._accounts[from].balance, 10'000'000'000);
}

TEST(Evm, dont_transfer_on_delegatecall)
{
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 5;
    s._accounts[to].balance = 0;

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
    EXPECT_EQ(s._accounts[from].balance, 10'000'000'000);
    EXPECT_EQ(s._accounts[to].balance, 0);
}

TEST(Evm, dont_transfer_on_staticcall)
{
    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xdac17f958d2ee523a2206206994597c13d831ec7_address};
    static fake::State::ChangeSet s{};
    s._accounts[from].balance = 10'000'000'000;
    s._accounts[from].nonce = 5;
    s._accounts[to].balance = 0;

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
    EXPECT_EQ(s._accounts[from].balance, 10'000'000'000);
    EXPECT_EQ(s._accounts[to].balance, 0);
}

TEST(Evm, create_contract_account)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto new_addr{
        0x58f3f9ebd5dbdf751f12d747b02d00324837077d_address};
    fake::State::ChangeSet s{};

    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 50'000u, .nonce = 1});
    traits_t::_store_contract_result.status_code = EVMC_SUCCESS;
    traits_t::_store_contract_result.gas_left = 10'000;
    traits_t::_store_contract_result.create_address = null;
    byte_string code{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07};
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_SUCCESS, .gas_left = 8'000}};

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 12'000,
        .sender = from,
        .input_data = code.data(),
        .input_size = code.size()};
    uint256_t v{6'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::create_contract_account(&h, s, m);

    EXPECT_EQ(result.create_address, new_addr);
    EXPECT_EQ(s.get_balance(from), bytes32_t{44'000});
    EXPECT_EQ(s.get_balance(new_addr), bytes32_t{6'000});
}

TEST(Evm, create2_contract_account)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto new_addr2{
        0xe0e05f8f41129e2087ec0a3759810fdced46edd4_address};
    fake::State::ChangeSet s{};

    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 50'000u, .nonce = 1});
    traits_t::_store_contract_result.status_code = EVMC_SUCCESS;
    traits_t::_store_contract_result.gas_left = 10'000;
    traits_t::_store_contract_result.create_address = null;
    byte_string code{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07};
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_SUCCESS, .gas_left = 8'000}};

    evmc_message m{
        .kind = EVMC_CREATE2,
        .gas = 18'000,
        .sender = from,
        .input_data = code.data(),
        .input_size = code.size(),
        .create2_salt = {}};
    uint256_t v{6'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::create_contract_account(&h, s, m);

    EXPECT_EQ(result.create_address, new_addr2);
    EXPECT_EQ(s.get_balance(from), bytes32_t{44'000});
    EXPECT_EQ(s.get_balance(new_addr2), bytes32_t{6'000});
}

TEST(Evm, oog_create_account)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 10'000, .nonce = 1});
    traits_t::_store_contract_result.status_code = EVMC_OUT_OF_GAS;
    traits_t::_store_contract_result.gas_left = 0;
    traits_t::_store_contract_result.create_address = null;

    evmc_message m{.kind = EVMC_CREATE, .gas = 12'000, .sender = from};

    auto const result = evm_t::create_contract_account(&h, s, m);

    EXPECT_TRUE(s._accounts.empty()); // revert was called on the fake
    EXPECT_EQ(result.status_code, EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.create_address, null);
    EXPECT_EQ(result.gas_left, 0);
}

TEST(Evm, revert_create_account)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto null{
        0x0000000000000000000000000000000000000000_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 10'000});
    traits_t::_store_contract_result.status_code = EVMC_SUCCESS;
    traits_t::_store_contract_result.gas_left = 10'000;
    traits_t::_store_contract_result.create_address = null;
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_REVERT, .gas_left = 11'000}};

    evmc_message m{.kind = EVMC_CREATE, .gas = 12'000, .sender = from};

    auto const result = evm_t::create_contract_account(&h, s, m);

    EXPECT_TRUE(s._accounts.empty()); // revert was called on the fake
    EXPECT_EQ(result.status_code, EVMC_REVERT);
    EXPECT_EQ(result.create_address, null);
    EXPECT_EQ(result.gas_left, 11'000);
}

TEST(Evm, call_evm)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto to{
        0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 50'000u});
    s._accounts.emplace(to, Account{.balance = 50'000u});
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_SUCCESS, .gas_left = 7'000}};

    evmc_message m{
        .kind = EVMC_CALL, .gas = 12'000, .recipient = to, .sender = from};
    uint256_t v{6'000};
    intx::be::store(m.value.bytes, v);

    auto const result = evm_t::call_evm(&h, s, m);

    EXPECT_EQ(s._accounts[from].balance, 44'000);
    EXPECT_EQ(s._accounts[to].balance, 56'000);
    EXPECT_EQ(result.gas_left, 7'000);
}

TEST(Evm, static_precompile_execution)
{
    using beta_traits_t = fake::traits::beta<fake::State::ChangeSet>;
    using alpha_evm_t = evm_t;
    using beta_evm_t = traits_templated_evm_t<beta_traits_t>;

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000001_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 15'000});
    s._accounts.emplace(code_address, Account{.nonce = 4});

    static constexpr char data[] = "hello world";
    static constexpr auto data_size = sizeof(data);

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 400,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<unsigned char const *>(data),
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
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000001_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 15'000});
    s._accounts.emplace(code_address, Account{.nonce = 6});

    static constexpr char data[] = "hello world";
    static constexpr auto data_size = sizeof(data);

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 100,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<unsigned char const *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address};

    evmc::Result const result = evm_t::call_evm(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_OUT_OF_GAS);
}

TEST(Evm, revert_call_evm)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000003_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 15'000});
    s._accounts.emplace(code_address, Account{.nonce = 10});
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
    EXPECT_TRUE(s._accounts.empty()); // revert was called on the fake
    EXPECT_EQ(result.gas_left, 6'000);
}
