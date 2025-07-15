#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_mainnet_alloc.hpp>
#include <category/execution/monad/chain/monad_revision.h>
#include <category/execution/ethereum/core/block.hpp>

#include <evmc/evmc.hpp>

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
    BlockHeader header;
    header.gas_limit = 5000;
    header.extra_data =
        evmc::from_hex(
            "5fc30e623b72ee612c7b388f75c562de73ee347cc2437c4562dee137e386dc0d")
            .value();
    header.base_fee_per_gas = 0;
    header.withdrawals_root = NULL_ROOT;
    header.blob_gas_used = 0;
    header.excess_blob_gas = 0;
    header.parent_beacon_block_root = NULL_ROOT;
    return {header, MONAD_MAINNET_ALLOC};
}

MONAD_NAMESPACE_END
