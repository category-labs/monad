#include <monad/chain/chain.hpp>

#include <monad/config.hpp>
#include <monad/core/result.hpp>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

Chain::Chain(uint64_t const block_number, uint64_t const timestamp)
    : block_number_{block_number}
    , timestamp_{timestamp}
{
}

Result<void> Chain::static_validate_header(BlockHeader const &) const
{
    return success();
}

MONAD_NAMESPACE_END
