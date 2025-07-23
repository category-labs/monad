#include <category/core/byte_string.hpp>
#include <category/execution/monad/system_call.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace evmc::literals;
using namespace intx::literals;
using namespace monad;

namespace
{
    evmc_message valid_syscall{
        .kind = EVMC_CALL,
        .flags = 0,
        .depth = 0,
        .gas = 0,
        .recipient = 0x1000_address,
        .sender = SYSTEM_TRANSACTION_SENDER,
        .input_data = nullptr,
        .input_size = 0,
        .value = {},
        .create2_salt = {},
        .code_address = 0x1000_address,
        .code = nullptr,
        .code_size = 0,
    };
}

TEST(SystemCall, valid)
{
    evmc_message good = valid_syscall;
    EXPECT_FALSE(is_restricted_system_call(good));

    // input doesn't matter
    byte_string_fixed<8> input_bytes{
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
    good.input_data = input_bytes.data();
    good.input_size = input_bytes.size();
    EXPECT_FALSE(is_restricted_system_call(good));
}

TEST(SystemCall, code_address_recipient_dont_match)
{
    evmc_message bad = valid_syscall;
    bad.code_address = 0x1000_address;
    bad.recipient = 0x2000_address;
    EXPECT_TRUE(is_restricted_system_call(bad));
}

TEST(SystemCall, invalid_sender)
{
    evmc_message bad = valid_syscall;
    bad.sender = 0xdeadbeef_address;
    EXPECT_TRUE(is_restricted_system_call(bad));
}

TEST(SystemCall, invoked_by_smart_contract)
{
    evmc_message bad = valid_syscall;
    bad.depth = 1;
    EXPECT_TRUE(is_restricted_system_call(bad));
}

TEST(SystemCall, uses_gas)
{
    evmc_message bad = valid_syscall;
    bad.gas = 10'000;
    EXPECT_TRUE(is_restricted_system_call(bad));
}

TEST(SystemCall, transfer)
{
    evmc_message bad = valid_syscall;
    bad.value = intx::be::store<evmc_uint256be>(1000_u256);
    EXPECT_TRUE(is_restricted_system_call(bad));
}

TEST(SystemCall, only_call_supported)
{
    for (int kind = EVMC_DELEGATECALL; kind <= EVMC_EOFCREATE; ++kind) {
        evmc_message bad = valid_syscall;
        bad.kind = static_cast<evmc_call_kind>(kind);
        EXPECT_TRUE(is_restricted_system_call(bad));
    }
}
