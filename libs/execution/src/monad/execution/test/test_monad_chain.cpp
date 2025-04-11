#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(MonadChain, compute_gas_refund)
{
    MonadTestnet monad_chain;
    Transaction tx{.gas_limit = 21'000};

    BlockHeader before_fork{.number = 0, .timestamp = 0};
    BlockHeader after_fork{.number = 1, .timestamp = 1739559600};

    auto const refund_before_fork = monad_chain.compute_gas_refund(
        before_fork.number, before_fork.timestamp, tx, 20'000, 1000);
    auto const refund_after_fork = monad_chain.compute_gas_refund(
        after_fork.number, after_fork.timestamp, tx, 20'000, 1000);
    EXPECT_EQ(20'200, refund_before_fork - refund_after_fork);
}

TEST(MonadChain, get_max_code_size)
{
    MonadTestnet const chain;
    EXPECT_EQ(chain.get_max_code_size(0, 1739559600), MAX_CODE_SIZE_EIP170);
    EXPECT_EQ(chain.get_max_code_size(0, 1741978800), 128 * 1024);
}
