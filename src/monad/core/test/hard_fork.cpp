#include <monad/config.hpp>
#include <monad/core/hard_fork.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(hard_fork, frontier)
{
    hard_fork::frontier f{};
    Transaction t{};
    EXPECT_EQ(f.intrinsic_gas(t), 21'000);

    t.data.push_back(0x00);
    EXPECT_EQ(f.intrinsic_gas(t), 21'004);

    t.data.push_back(0xff);
    EXPECT_EQ(f.intrinsic_gas(t), 21'072);
}

TEST(hard_fork, homestead)
{
    hard_fork::homestead h{};
    Transaction t{};
    EXPECT_EQ(h.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(h.intrinsic_gas(t), 21'000);
}

TEST(hard_fork, intanbul)
{
    hard_fork::istanbul i{};
    Transaction t{};
    EXPECT_EQ(i.intrinsic_gas(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    t.data.push_back(0x00);
    EXPECT_EQ(i.intrinsic_gas(t), 21'004);

    t.data.push_back(0xff);
    EXPECT_EQ(i.intrinsic_gas(t), 21'020);
}

TEST(hard_fork, berlin)
{
    hard_fork::berlin b{};
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
