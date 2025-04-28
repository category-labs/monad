#include <monad/chain/monad_revision.h>
#include <monad/chain/monad_testnet.hpp>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

monad_revision MonadTestnet::get_monad_revision(
    uint64_t /* block_number */, uint64_t const timestamp) const
{
    if (MONAD_LIKELY(timestamp >= 1741978800)) { // 2025-03-14T19:00:00.000Z
        return MONAD_TWO;
    }
    else if (timestamp >= 1739559600) { // 2025-02-14T19:00:00.000Z
        return MONAD_ONE;
    }
    return MONAD_ZERO;
}

uint256_t MonadTestnet::get_chain_id() const
{
    return 10143;
};

MONAD_NAMESPACE_END
