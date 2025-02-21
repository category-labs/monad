#include <monad/chain/monad_testnet.hpp>
#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(MonadRefund, testnet_fork)
{
    MonadTestnet const monad_chain;
    Transaction const tx{.gas_limit = 21'000};

    BlockHeader const before_fork{.number = 0, .timestamp = 0};
    BlockHeader const after_fork{.number = 1, .timestamp = 1739559600};

    auto const refund_before_fork = monad_chain.compute_gas_refund(
        before_fork.number, before_fork.timestamp, tx, 20'000, 1000);
    auto const refund_after_fork = monad_chain.compute_gas_refund(
        after_fork.number, after_fork.timestamp, tx, 20'000, 1000);
    EXPECT_EQ(20'200, refund_before_fork - refund_after_fork);
}
