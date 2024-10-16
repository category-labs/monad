#pragma once

#include <monad/chain/ethereum_mainnet.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

// Ethereum tests pass in the revision explicitly. Block numbers in the tests
// always resolve to frontier.
class EthereumTestChain : public EthereumMainnet
{
private:
    evmc_revision rev_;

public:
    explicit EthereumTestChain(evmc_revision const rev)
        : rev_(rev)
    {
    }

    virtual evmc_revision get_revision(uint64_t, uint64_t) const override
    {
        return rev_;
    }
};

MONAD_NAMESPACE_END
