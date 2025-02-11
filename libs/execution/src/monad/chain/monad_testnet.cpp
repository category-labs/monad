#include <monad/chain/monad_testnet.hpp>

#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

monad_revision MonadTestnet::get_monad_revision(uint64_t, uint64_t) const
{
    return MONAD_ZERO;
}

uint256_t MonadTestnet::get_chain_id() const
{
    return 10143;
};

MONAD_NAMESPACE_END
