#include <category/core/byte_string.hpp>
#include <monad/execution/create_contract_address.hpp>

#include <evmc/evmc.hpp>

#include <ethash/keccak.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;

TEST(Execution, create_contract_address)
{
    // USDT Stablecoin contract
    EXPECT_EQ(
        create_contract_address(
            0x36928500bc1dcd7af6a2b4008875cc336b927d57_address, 6),
        0xdac17f958d2ee523a2206206994597c13d831ec7_address);
}

TEST(Execution, create2_contract_address)
{
    // all examples from EIP-1014
    static constexpr auto null_salt{
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32};
    static constexpr auto feed_salt{
        0x000000000000000000000000feed000000000000000000000000000000000000_bytes32};
    static constexpr auto cafebabe_salt{
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32};
    static uint8_t const zero[1]{0x00};
    static uint8_t const deadbeef[4]{0xde, 0xad, 0xbe, 0xef};
    static byte_string const deadcattle{
        0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe,
        0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad,
        0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde,
        0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef};

    auto const zero_hash = ethash::keccak256(&zero[0], 1);
    EXPECT_EQ(
        create2_contract_address(
            0x0000000000000000000000000000000000000000_address,
            null_salt,
            zero_hash),
        0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38_address);

    EXPECT_EQ(
        create2_contract_address(
            0xdeadbeef00000000000000000000000000000000_address,
            null_salt,
            zero_hash),
        0xB928f69Bb1D91Cd65274e3c79d8986362984fDA3_address);

    EXPECT_EQ(
        create2_contract_address(
            0xdeadbeef00000000000000000000000000000000_address,
            feed_salt,
            zero_hash),
        0xD04116cDd17beBE565EB2422F2497E06cC1C9833_address);

    auto const deadbeef_hash = ethash::keccak256(&deadbeef[0], 4);
    EXPECT_EQ(
        create2_contract_address(
            0x0000000000000000000000000000000000000000_address,
            null_salt,
            deadbeef_hash),
        0x70f2b2914A2a4b783FaEFb75f459A580616Fcb5e_address);

    EXPECT_EQ(
        create2_contract_address(
            0x00000000000000000000000000000000deadbeef_address,
            cafebabe_salt,
            deadbeef_hash),
        0x60f3f640a8508fC6a86d45DF051962668E1e8AC7_address);

    auto const deadcattle_hash =
        ethash::keccak256(deadcattle.data(), deadcattle.size());
    EXPECT_EQ(
        create2_contract_address(
            0x00000000000000000000000000000000deadbeef_address,
            cafebabe_salt,
            deadcattle_hash),
        0x1d8bfDC5D46DC4f61D6b6115972536eBE6A8854C_address);

    auto const null_hash = ethash::keccak256(nullptr, 0);
    EXPECT_EQ(
        create2_contract_address(
            0x0000000000000000000000000000000000000000_address,
            null_salt,
            null_hash),
        0xE33C0C7F7df4809055C3ebA6c09CFe4BaF1BD9e0_address);
}
