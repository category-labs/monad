#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

Result<void> MonadChain::validate_output_header(
    BlockHeader const &input, BlockHeader const &output) const
{
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }
    return success();
}

evmc_revision MonadChain::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    switch (get_monad_revision(block_number, timestamp)) {
    case MONAD_ZERO:
        return EVMC_CANCUN;
    }
    MONAD_ABORT("bad revision");
}

uint64_t MonadChain::compute_gas_refund(
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, uint64_t const gas_remaining,
    uint64_t const refund) const
{
    switch (get_monad_revision(block_number, timestamp)) {
    case MONAD_ZERO: {
        auto const evmc_rev = get_revision(block_number, timestamp);
        return g_star(evmc_rev, tx, gas_remaining, refund);
    }
    }
    MONAD_ABORT("bad revision");
}

MONAD_NAMESPACE_END
