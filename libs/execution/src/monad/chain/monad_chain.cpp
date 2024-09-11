#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/intrinsic_gas_buffer.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state3/state.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

namespace
{
    uint256_t effective_reserve(
        IntrinsicGasBuffer const &buf, uint256_t const &max_reserve,
        Address const &addr, uint256_t const &balance)
    {
        if (balance < max_reserve) {
            return balance;
        }
        uint256_t const gas = buf.sum(addr);
        // TODO: permissible with variable reserve
        MONAD_ASSERT(gas <= max_reserve);
        return max_reserve - gas;
    }

    uint256_t
    effective_balance(uint256_t const &max_reserve, uint256_t const &balance)
    {
        return balance <= max_reserve ? uint256_t{0} : balance - max_reserve;
    }
}

MonadChain::MonadChain(
    IntrinsicGasBuffer &buf, uint256_t const &default_max_reserve)
    : buf_{buf}
    , default_max_reserve_{default_max_reserve}
{
}

Result<void> MonadChain::validate_header(
    std::vector<Receipt> const &, BlockHeader const &) const
{
    // TODO
    return success();
}

bool MonadChain::validate_root(
    evmc_revision const, BlockHeader const &, bytes32_t const &,
    bytes32_t const &) const
{
    // TODO
    return true;
}

Result<void> MonadChain::validate_transaction(
    evmc_revision const rev, Transaction const &tx, Address const &sender,
    std::optional<Account> const &acc) const
{
    auto res = ::monad::validate_transaction(tx, acc);
    if (res.has_error() &&
        res.error() != TransactionError::InsufficientBalance) {
        return res;
    }

    uint256_t const balance = acc.has_value() ? acc->balance : uint256_t{0};
    if (max_gas_cost(intrinsic_gas(rev, tx), tx.max_fee_per_gas) >
        effective_reserve(buf_, default_max_reserve_, sender, balance)) {
        return TransactionError::InsufficientReserveBalance;
    }

    return success();
}

evmc::Result MonadChain::execute_impl_no_validation(
    CallTracerBase &call_tracer, evmc_revision const rev,
    BlockHashBuffer const &buf, BlockHeader const &hdr, State &state,
    Transaction const &tx, Address const &sender,
    std::optional<Account> const &acct)
{
    // Note: Intrinsic gas charged from the reserve balance
    uint512_t const v0 =
        tx.value +
        max_gas_cost(tx.gas_limit - intrinsic_gas(rev, tx), tx.max_fee_per_gas);
    auto const balance = acct.has_value() ? acct->balance : uint256_t{0};
    if (effective_balance(default_max_reserve_, balance) < v0) {
        return evmc::Result{EVMC_REJECTED};
    }
    auto res = ::monad::execute_impl_no_validation(
        call_tracer, rev, buf, hdr, get_chain_id(), state, tx, sender);
    MONAD_ASSERT(res.status_code != EVMC_REJECTED);
    return res;
}

Receipt MonadChain::execute_final(
    evmc_revision const rev, State &state, Transaction const &tx,
    Address const &sender, uint256_t const &base_fee_per_gas,
    evmc::Result const &result, Address const &beneficiary)
{
    auto const gas = intrinsic_gas(rev, tx);
    auto const price = gas_price(rev, tx, base_fee_per_gas);
    buf_.add(sender, gas * price);
    if (result.status_code == EVMC_REJECTED) {
        auto const nonce = state.get_nonce(sender);
        state.set_nonce(sender, nonce + 1);
        state.subtract_from_balance(sender, gas * price);
        return Receipt{.status = 0, .gas_used = gas, .type = tx.type};
    }
    return ::monad::execute_final(
        rev, state, tx, sender, base_fee_per_gas, result, beneficiary);
}

MONAD_NAMESPACE_END
