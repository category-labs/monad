#include <monad/chain/monad_mainnet.hpp>
#include <monad/chain/monad_revision.h>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

monad_revision MonadMainnet::get_monad_revision(
    uint64_t /* block_number */, uint64_t /* timstamp */) const
{
    return MONAD_TWO;
}

uint256_t MonadMainnet::get_chain_id() const
{
    return 143;
}

GenesisState MonadMainnet::get_genesis_state() const
{
    MONAD_ASSERT_PRINTF(false, "TODO");
    return {};
}

MONAD_NAMESPACE_END
