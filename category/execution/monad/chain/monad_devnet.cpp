#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_devnet_alloc.hpp>
#include <category/execution/monad/chain/monad_revision.h>
#include <category/core/config.hpp>
#include <category/core/int.hpp>

MONAD_NAMESPACE_BEGIN

monad_revision MonadDevnet::get_monad_revision(
    uint64_t /* block_number */, uint64_t /* timestamp */) const
{
    return MONAD_THREE;
}

uint256_t MonadDevnet::get_chain_id() const
{
    return 20143;
};

GenesisState MonadDevnet::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 17179869184;
    header.gas_limit = 5000;
    intx::be::unsafe::store<uint64_t>(header.nonce.data(), 66);
    header.extra_data = evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                       "db3db69cbdb7a38e1e50b1b82fa")
                            .value();
    return {header, MONAD_DEVNET_ALLOC};
}

MONAD_NAMESPACE_END
