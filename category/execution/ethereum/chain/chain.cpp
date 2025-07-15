#include <category/execution/ethereum/chain/chain.hpp>

#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

Result<void> Chain::static_validate_header(BlockHeader const &) const
{
    return success();
}

MONAD_NAMESPACE_END
