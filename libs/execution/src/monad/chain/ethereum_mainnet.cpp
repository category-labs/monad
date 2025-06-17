#include <monad/chain/ethereum_mainnet.hpp>

#include <monad/chain/ethereum_mainnet_alloc.hpp>
#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>

#include <limits>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

uint256_t EthereumMainnet::get_chain_id() const
{
    return 1;
};

evmc_revision EthereumMainnet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    // TODO: update to include Prague once we can replay those blocks

    if (MONAD_LIKELY(timestamp >= 1710338135)) {
        return EVMC_CANCUN;
    }
    else if (timestamp >= 1681338455) {
        return EVMC_SHANGHAI;
    }
    else if (block_number >= 15537394) {
        return EVMC_PARIS;
    }
    else if (block_number >= 12965000) {
        return EVMC_LONDON;
    }
    else if (block_number >= 12244000) {
        return EVMC_BERLIN;
    }
    else if (block_number >= 9069000) {
        return EVMC_ISTANBUL;
    }
    else if (block_number >= 7280000) {
        return EVMC_PETERSBURG;
    }
    else if (block_number >= 4370000) {
        return EVMC_BYZANTIUM;
    }
    else if (block_number >= 2675000) {
        return EVMC_SPURIOUS_DRAGON;
    }
    else if (block_number >= 2463000) {
        return EVMC_TANGERINE_WHISTLE;
    }
    else if (block_number >= 1150000) {
        return EVMC_HOMESTEAD;
    }
    return EVMC_FRONTIER;
}

Result<void>
EthereumMainnet::static_validate_header(BlockHeader const &header) const
{
    // EIP-779
    if (MONAD_UNLIKELY(
            header.number >= dao::dao_block_number &&
            header.number <= dao::dao_block_number + 9 &&
            header.extra_data != dao::extra_data)) {
        return BlockError::WrongDaoExtraData;
    }
    return success();
}

Result<void> EthereumMainnet::validate_output_header(
    BlockHeader const &input, BlockHeader const &output) const
{
    // First, validate execution inputs.
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // Second, validate execution outputs known before commit.

    // YP eq. 170
    if (MONAD_UNLIKELY(input.gas_used != output.gas_used)) {
        return BlockError::InvalidGasUsed;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }

    // YP eq. 33
    if (MONAD_UNLIKELY(input.logs_bloom != output.logs_bloom)) {
        return BlockError::WrongLogsBloom;
    }

    if (MONAD_UNLIKELY(input.parent_hash != output.parent_hash)) {
        return BlockError::WrongParentHash;
    }

    // Lastly, validate execution outputs only known after commit.
    if (MONAD_UNLIKELY(input.state_root != output.state_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.receipts_root != output.receipts_root)) {
        return BlockError::WrongMerkleRoot;
    }

    return success();
}

uint64_t EthereumMainnet::compute_gas_refund(
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, uint64_t const gas_remaining,
    uint64_t const refund) const
{
    auto const rev = get_revision(block_number, timestamp);
    return g_star(rev, tx, gas_remaining, refund);
}

size_t EthereumMainnet::get_max_code_size(
    uint64_t const block_number, uint64_t const timestamp) const
{
    return get_revision(block_number, timestamp) >= EVMC_SPURIOUS_DRAGON
               ? MAX_CODE_SIZE_EIP170
               : std::numeric_limits<size_t>::max();
}

GenesisState EthereumMainnet::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 17179869184;
    header.gas_limit = 5000;
    intx::be::unsafe::store<uint64_t>(header.nonce.data(), 66);
    header.extra_data = evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                       "db3db69cbdb7a38e1e50b1b82fa")
                            .value();
    return {header, ETHEREUM_MAINNET_ALLOC};
}

bool EthereumMainnet::get_create_inside_delegated() const
{
    return true;
}

MONAD_NAMESPACE_END
