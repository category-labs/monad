#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/execution/validation_status.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <algorithm>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

// YP Sec 6.2 "irrevocable_change"
template <evmc_revision rev>
constexpr void irrevocable_change(
    State &state, Transaction const &txn, uint256_t const &base_fee_per_gas)
{
    if (txn.to) { // EVM will increment if new contract
        auto const nonce = state.get_nonce(*txn.from);
        state.set_nonce(*txn.from, nonce + 1);
    }
    MONAD_DEBUG_ASSERT(txn.from.has_value());

    auto const upfront_cost =
        txn.gas_limit * gas_price<rev>(txn, base_fee_per_gas);
    state.subtract_from_balance(txn.from.value(), upfront_cost);
}

// YP Eqn 72
template <evmc_revision rev>
constexpr uint64_t g_star(
    Transaction const &txn, uint64_t const gas_remaining, uint64_t const refund)
{
    // EIP-3529
    constexpr auto max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
    auto const refund_allowance =
        (txn.gas_limit - gas_remaining) / max_refund_quotient;

    return gas_remaining + std::min(refund_allowance, refund);
}

template <evmc_revision rev>
constexpr auto refund_gas(
    State &state, Transaction const &txn, uint256_t const &base_fee_per_gas,
    uint64_t const gas_leftover, uint64_t const refund)
{
    // refund and priority, Eqn. 73-76
    auto const gas_remaining = g_star<rev>(txn, gas_leftover, refund);
    auto const gas_cost = gas_price<rev>(txn, base_fee_per_gas);

    MONAD_DEBUG_ASSERT(txn.from.has_value());
    state.add_to_balance(txn.from.value(), gas_cost * gas_remaining);

    return gas_remaining;
}

template <evmc_revision rev>
constexpr evmc_message to_message(Transaction const &tx)
{
    auto const to_address = [&tx] {
        if (tx.to) {
            return std::pair{EVMC_CALL, *tx.to};
        }
        return std::pair{EVMC_CREATE, address_t{}};
    }();

    evmc_message msg{
        .kind = to_address.first,
        .gas = static_cast<int64_t>(tx.gas_limit - intrinsic_gas<rev>(tx)),
        .recipient = to_address.second,
        .sender = *tx.from,
        .input_data = tx.data.data(),
        .input_size = tx.data.size(),
        .code_address = to_address.second,
    };
    intx::be::store(msg.value.bytes, tx.value);
    return msg;
}

template <evmc_revision rev>
Receipt execute(
    State &state, EvmcHost<rev> &host, Transaction const &tx,
    uint256_t const &base_fee_per_gas, address_t const &beneficiary)
{
    irrevocable_change<rev>(state, tx, base_fee_per_gas);

    // EIP-3651
    if constexpr (rev >= EVMC_SHANGHAI) {
        host.access_account(beneficiary);
    }

    state.access_account(*tx.from);
    for (auto const &ae : tx.access_list) {
        state.access_account(ae.a);
        for (auto const &keys : ae.keys) {
            state.access_storage(ae.a, keys);
        }
    }
    if (tx.to) {
        state.access_account(*tx.to);
    }

    auto const msg = to_message<rev>(tx);
    auto const result = host.call(msg);

    MONAD_DEBUG_ASSERT(result.gas_left >= 0);
    MONAD_DEBUG_ASSERT(result.gas_refund >= 0);
    MONAD_DEBUG_ASSERT(tx.gas_limit >= static_cast<uint64_t>(result.gas_left));
    auto const gas_remaining = refund_gas<rev>(
        state,
        tx,
        base_fee_per_gas,
        static_cast<uint64_t>(result.gas_left),
        static_cast<uint64_t>(result.gas_refund));
    auto const gas_used = tx.gas_limit - gas_remaining;
    auto const reward =
        calculate_txn_award<rev>(tx, base_fee_per_gas, gas_used);
    state.add_to_balance(beneficiary, reward);

    // finalize state, Eqn. 77-79
    state.destruct_suicides();
    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    Receipt receipt{
        .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
        .gas_used = gas_used,
        .type = tx.type};
    for (auto &log : state.logs()) {
        receipt.add_log(std::move(log));
    }

    return receipt;
}

EXPLICIT_EVMC_REVISION(execute);

template <evmc_revision rev>
ValidationStatus validate_and_execute(
    Transaction const &tx, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, State &state, Receipt &receipt)
{
    MONAD_DEBUG_ASSERT(
        static_validate_transaction<rev>(tx, hdr.base_fee_per_gas) ==
        ValidationStatus::SUCCESS);

    if (auto const validity = validate_transaction(state, tx);
        validity != ValidationStatus::SUCCESS) {
        // TODO: Issue #164, Issue #54
        return validity;
    }

    auto const tx_context = get_tx_context<rev>(tx, hdr);
    EvmcHost<rev> host{tx_context, block_hash_buffer, state};
    receipt = execute<rev>(
        state, host, tx, hdr.base_fee_per_gas.value_or(0), hdr.beneficiary);

    return ValidationStatus::SUCCESS;
}

EXPLICIT_EVMC_REVISION(validate_and_execute);

MONAD_NAMESPACE_END
