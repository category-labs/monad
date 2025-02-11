#include <monad/chain/monad_devnet.hpp>

#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

monad_revision MonadDevnet::get_monad_revision(uint64_t, uint64_t) const
{
    return MONAD_ZERO;
}

uint256_t MonadDevnet::get_chain_id() const
{
    return 20143;
};

MONAD_NAMESPACE_END
