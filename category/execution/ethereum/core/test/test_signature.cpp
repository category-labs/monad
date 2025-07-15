#include <category/execution/ethereum/core/signature.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(Signature, get_v)
{
    // Legacy - no chain id
    EXPECT_EQ(get_v({.y_parity = false}), 27);
    EXPECT_EQ(get_v({.y_parity = true}), 28);
    // EIP-155
    EXPECT_EQ(get_v({.chain_id = 1, .y_parity = false}), 37);
    EXPECT_EQ(get_v({.chain_id = 1, .y_parity = true}), 38);
    EXPECT_EQ(get_v({.chain_id = 5, .y_parity = false}), 45);
    EXPECT_EQ(get_v({.chain_id = 5, .y_parity = true}), 46);
}

TEST(Signature, from_v)
{
    // Legacy - no chain id
    {
        SignatureAndChain sc{};
        sc.from_v(27);
        EXPECT_EQ(sc.y_parity, false);
        sc.from_v(28);
        EXPECT_EQ(sc.y_parity, true);
    }

    // EIP-155
    {
        SignatureAndChain sc{};
        sc.from_v(37);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.y_parity, false);
        sc.from_v(38);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.y_parity, true);
    }
    {
        SignatureAndChain sc{};
        sc.from_v(45);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.y_parity, false);
        sc.from_v(46);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.y_parity, true);
    }
}
