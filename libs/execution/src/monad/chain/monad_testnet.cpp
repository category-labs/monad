#include <monad/chain/monad_testnet.hpp>

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

uint256_t MonadTestnet::get_chain_id() const
{
    return 10143;
};

evmc_revision MonadTestnet::get_revision(uint64_t const, uint64_t const) const
{
    return EVMC_SHANGHAI;
}

MONAD_NAMESPACE_END
