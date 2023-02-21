#include <gtest/gtest.h>
#include <monad/core/signature.hpp>
#include <monad/rlp/encode_helpers.hpp>

using namespace monad;

TEST(Signature, get_v)
{
    // Legacy - no chain id
    EXPECT_EQ(get_v({.odd_y_parity = false}), 27);
    EXPECT_EQ(get_v({.odd_y_parity = true}), 28);
    // EIP-155
    EXPECT_EQ(get_v({.chain_id = 1, .odd_y_parity = false}), 37);
    EXPECT_EQ(get_v({.chain_id = 1, .odd_y_parity = true}), 38);
    EXPECT_EQ(get_v({.chain_id = 5, .odd_y_parity = false}), 45);
    EXPECT_EQ(get_v({.chain_id = 5, .odd_y_parity = true}), 46);
}

TEST(Signature, from_v)
{
    // Legacy - no chain id
    {
        SignatureAndChain sc{};
        sc.from_v(27);
        EXPECT_EQ(sc.odd_y_parity, false);
        sc.from_v(28);
        EXPECT_EQ(sc.odd_y_parity, true);
    }

    // EIP-155
    {
        SignatureAndChain sc{};
        sc.from_v(37);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.odd_y_parity, false);
        sc.from_v(38);
        EXPECT_EQ(sc.chain_id, 1);
        EXPECT_EQ(sc.odd_y_parity, true);
    }
    {
        SignatureAndChain sc{};
        sc.from_v(45);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.odd_y_parity, false);
        sc.from_v(46);
        EXPECT_EQ(sc.chain_id, 5);
        EXPECT_EQ(sc.odd_y_parity, true);
    }
}
