#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

Result<void> MonadChain::validate_header(
    std::vector<Receipt> const &, BlockHeader const &) const
{
    // TODO
    return success();
}

bool MonadChain::validate_root(
    evmc_revision const, BlockHeader const &, bytes32_t const &,
    bytes32_t const &, bytes32_t const &,
    std::optional<bytes32_t> const &) const
{
    // TODO
    return true;
}

MONAD_NAMESPACE_END
