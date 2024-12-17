#include <monad/chain/ethereum_mainnet.hpp>

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/validate_block.hpp>

#include <evmc/evmc.h>

#include <quill/Quill.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

uint256_t EthereumMainnet::get_chain_id() const
{
    return 1;
};

evmc_revision EthereumMainnet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    if (timestamp >= 1710338135) {
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

Result<void> EthereumMainnet::validate_header(
    std::vector<Receipt> const &receipts, BlockHeader const &hdr) const
{
    // YP eq. 33
    if (MONAD_UNLIKELY(compute_bloom(receipts) != hdr.logs_bloom)) {
        return BlockError::WrongLogsBloom;
    }

    // YP eq. 170
    if (MONAD_UNLIKELY(
            !receipts.empty() && receipts.back().gas_used != hdr.gas_used)) {
        return BlockError::InvalidGasUsed;
    }

    return success();
}

bool EthereumMainnet::validate_root(
    evmc_revision const rev, BlockHeader const &hdr,
    bytes32_t const &state_root, bytes32_t const &receipts_root,
    bytes32_t const &transactions_root,
    std::optional<bytes32_t> const &withdrawals_root) const
{
    if (MONAD_UNLIKELY(state_root != hdr.state_root)) {
        LOG_ERROR(
            "Block: {}, Computed State Root: {}, Expected State Root: {}",
            hdr.number,
            state_root,
            hdr.state_root);
        return false;
    }
    if (MONAD_LIKELY(rev >= EVMC_BYZANTIUM)) {
        if (MONAD_UNLIKELY(receipts_root != hdr.receipts_root)) {
            LOG_ERROR(
                "Block: {}, Computed Receipts Root: {}, Expected Receipts "
                "Root: {}",
                hdr.number,
                receipts_root,
                hdr.receipts_root);
            return false;
        }
    }
    if (MONAD_UNLIKELY(transactions_root != hdr.transactions_root)) {
        LOG_ERROR(
            "Block: {}, Computed Transactions Root: {}, Expected Transactions "
            "Root: {}",
            hdr.number,
            transactions_root,
            hdr.transactions_root);
        return false;
    }
    if (MONAD_UNLIKELY(withdrawals_root != hdr.withdrawals_root)) {
        LOG_ERROR(
            "Block: {}, Computed Withdrawals Root: {}, Expected Withdrawals "
            "Root: {}",
            hdr.number,
            withdrawals_root,
            hdr.withdrawals_root);
        return false;
    }
    return true;
}

MONAD_NAMESPACE_END
