#include <monad/config.hpp>
#include <monad/core/hard_fork.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(HardFork, genesis)
{
    hard_fork::genesis g{};
    Transaction t{};
    EXPECT_EQ(g.base_gas_cost(t), 21'000);
}

TEST(HardFork, homestead)
{
    hard_fork::homestead h{};
    Transaction t{};
    EXPECT_EQ(h.base_gas_cost(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(h.base_gas_cost(t), 21'000);
}
