#include <monad/chain/monad_devnet.hpp>

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

uint256_t MonadDevnet::get_chain_id() const
{
    return 20143;
};

evmc_revision MonadDevnet::get_revision(uint64_t const, uint64_t const) const
{
    return EVMC_CANCUN;
}

MONAD_NAMESPACE_END
