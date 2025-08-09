#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/fee_buffer.hpp>
#include <category/execution/monad/reserve_balance.h>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

evmc_revision MonadChain::get_revision(
    uint64_t /* block_number */, uint64_t /* timestamp */) const
{
    return EVMC_CANCUN;
}

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

uint64_t MonadChain::compute_gas_refund(
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, uint64_t const gas_remaining,
    uint64_t const refund) const
{
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_ONE)) {
        return 0;
    }
    else if (monad_rev == MONAD_ZERO) {
        auto const rev = get_revision(block_number, timestamp);
        return g_star(rev, tx, gas_remaining, refund);
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

size_t MonadChain::get_max_code_size(
    uint64_t const block_number, uint64_t const timestamp) const
{
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_TWO)) {
        return 128 * 1024;
    }
    else if (monad_rev >= MONAD_ZERO) {
        return MAX_CODE_SIZE_EIP170;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

Result<void> MonadChain::validate_transaction(
    uint64_t const block_number, uint64_t const timestamp, uint64_t const i,
    Transaction const &tx, Address const &sender, State &state,
    void *const chain_context) const
{
    auto const acct = state.recent_account(sender);
    auto res = ::monad::validate_transaction(tx, acct);
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }
        auto const &context = *static_cast<MonadChainContext *>(chain_context);
        auto const [cum_fee, tx_fee, _] = context.fee_buffer.get(i, sender);
        MONAD_ASSERT(cum_fee >= tx_fee);
        uint512_t const cum_fees_without_tx = cum_fee - tx_fee;
        uint512_t const max_reserve = get_max_reserve(monad_rev, sender);
        uint512_t const balance = acct.has_value() ? acct.value().balance : 0;
        uint512_t const reserve = std::min(
            balance, max_reserve - std::min(max_reserve, cum_fees_without_tx));
        if (MONAD_UNLIKELY(tx_fee > reserve)) {
            return TransactionError::InsufficientReserveBalance;
        }
    }
    else if (monad_rev >= MONAD_ZERO) {
        return res;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
    return success();
}

bool MonadChain::revert_transaction(
    uint64_t const block_number, uint64_t const timestamp, uint64_t const i,
    Address const &sender, State const &state, void *const chain_context) const
{
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        auto const &orig = state.original();
        MONAD_ASSERT(orig.contains(sender));
        uint256_t const max_reserve = get_max_reserve(monad_rev, sender);
        MONAD_ASSERT(chain_context);
        auto const &ctx = *static_cast<MonadChainContext *>(chain_context);
        uint512_t const cum_fee = ctx.fee_buffer.get(i, sender).cumulative_fee;
        std::optional<Account> const &orig_account = orig.at(sender).account_;
        uint256_t const orig_balance =
            orig_account.has_value() ? orig_account.value().balance : 0;
        MONAD_ASSERT(cum_fee <= max_reserve);
        MONAD_ASSERT(cum_fee <= orig_balance);
        uint256_t const protected_balance = std::min(
            max_reserve - static_cast<uint256_t>(cum_fee), orig_balance);

        auto const &curr = state.current();
        MONAD_ASSERT(curr.contains(sender));
        auto const &stack = curr.at(sender);
        std::optional<Account> const &curr_account = stack.recent().account_;
        uint256_t const &curr_balance =
            curr_account.has_value() ? curr_account.value().balance : 0;

        return curr_balance < protected_balance;
    }
    else if (monad_rev >= MONAD_ZERO) {
        return false;
    }
    else {
        MONAD_ABORT("invalid revision for revert");
    }
}

uint256_t get_max_reserve(monad_revision const rev, Address const &)
{
    // TODO: implement precompile (support reading from orig)
    return monad_default_max_reserve_balance(rev);
}

MONAD_NAMESPACE_END
