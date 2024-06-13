#include <monad/chain/monad_devnet.hpp>

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/validate_block.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

uint256_t MonadDevnet::get_chain_id() const
{
    return 1;
};

evmc_revision MonadDevnet::get_revision(BlockHeader const &) const
{
    return EVMC_SHANGHAI;
}

Result<void>
MonadDevnet::static_validate_header(BlockHeader const &header) const
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

MONAD_NAMESPACE_END
