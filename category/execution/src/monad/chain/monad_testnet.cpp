#include <monad/chain/monad_revision.h>
#include <monad/chain/monad_testnet.hpp>
#include <monad/chain/monad_testnet_alloc.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>

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

GenesisState MonadTestnet::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 17179869184;
    header.gas_limit = 5000;
    intx::be::unsafe::store<uint64_t>(header.nonce.data(), 66);
    header.extra_data = evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                       "db3db69cbdb7a38e1e50b1b82fa")
                            .value();
    return {header, MONAD_TESTNET_ALLOC};
}

MONAD_NAMESPACE_END
