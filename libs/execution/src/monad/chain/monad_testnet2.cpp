#include <monad/chain/monad_revision.h>
#include <monad/chain/monad_testnet2.hpp>
#include <monad/chain/monad_testnet2_alloc.hpp>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

monad_revision MonadTestnet2::get_monad_revision(
    uint64_t /* block_number */, uint64_t /* timstamp */) const
{
    return MONAD_TWO;
}

uint256_t MonadTestnet2::get_chain_id() const
{
    return 30143;
};

GenesisState MonadTestnet2::get_genesis_state() const
{
    BlockHeader header;
    header.gas_limit = 5000;
    header.extra_data = evmc::from_hex("0x0000000000000000000000000000000000000"
                                       "000000000000000000000000000")
                            .value();
    header.base_fee_per_gas = 0;
    header.withdrawals_root = NULL_ROOT;
    header.blob_gas_used = 0;
    header.excess_blob_gas = 0;
    header.parent_beacon_block_root = NULL_ROOT;
    return {header, MONAD_TESTNET2_ALLOC};
}

MONAD_NAMESPACE_END
