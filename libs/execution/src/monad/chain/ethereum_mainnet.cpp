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

evmc_revision EthereumMainnet::get_revision(BlockHeader const &header) const
{
    if (header.number >= 17034870) {
        return EVMC_SHANGHAI;
    }
    else if (header.number >= 15537394) {
        return EVMC_PARIS;
    }
    else if (header.number >= 12965000) {
        return EVMC_LONDON;
    }
    else if (header.number >= 12244000) {
        return EVMC_BERLIN;
    }
    else if (header.number >= 9069000) {
        return EVMC_ISTANBUL;
    }
    else if (header.number >= 7280000) {
        return EVMC_PETERSBURG;
    }
    else if (header.number >= 4370000) {
        return EVMC_BYZANTIUM;
    }
    else if (header.number >= 2675000) {
        return EVMC_SPURIOUS_DRAGON;
    }
    else if (header.number >= 2463000) {
        return EVMC_TANGERINE_WHISTLE;
    }
    else if (header.number >= 1150000) {
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

bool EthereumMainnet::validate_root(
    evmc_revision const rev, BlockHeader const &hdr,
    bytes32_t const &state_root, bytes32_t const &receipts_root) const
{
    if (state_root != hdr.state_root) {
        LOG_ERROR(
            "Block: {}, Computed State Root: {}, Expected State Root: {}",
            hdr.number,
            state_root,
            hdr.state_root);
        return false;
    }
    if (MONAD_LIKELY(rev >= EVMC_BYZANTIUM)) {
        if (receipts_root != hdr.receipts_root) {
            LOG_ERROR(
                "Block: {}, Computed Receipts Root: {}, Expected Receipts "
                "Root: {}",
                hdr.number,
                receipts_root,
                hdr.receipts_root);
            return false;
        }
    }
    return true;
}

MONAD_NAMESPACE_END
