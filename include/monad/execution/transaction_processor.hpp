#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validation.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <algorithm>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
struct TransactionProcessor
{
    // YP Sec 6.2 "irrevocable_change"
    static constexpr void irrevocable_change(
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
    [[nodiscard]] static constexpr uint64_t g_star(
        Transaction const &txn, uint64_t const gas_remaining,
        uint64_t const refund)
    {
        // EIP-3529
        constexpr auto max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
        auto const refund_allowance =
            (txn.gas_limit - gas_remaining) / max_refund_quotient;

        return gas_remaining + std::min(refund_allowance, refund);
    }

    [[nodiscard]] static constexpr auto refund_gas(
        State &state, Transaction const &txn, uint256_t const &base_fee_per_gas,
        uint64_t const gas_leftover, uint64_t const refund)
    {
        // refund and priority, Eqn. 73-76
        auto const gas_remaining = g_star(txn, gas_leftover, refund);
        auto const gas_cost = gas_price<rev>(txn, base_fee_per_gas);

        MONAD_DEBUG_ASSERT(txn.from.has_value());
        state.add_to_balance(txn.from.value(), gas_cost * gas_remaining);

        return gas_remaining;
    }

    [[nodiscard]] static constexpr evmc_message
    to_message(Transaction const &tx)
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

    Receipt execute(
        State &state, EvmcHost<rev> &host, Transaction const &txn,
        uint256_t const &base_fee_per_gas, address_t const &beneficiary) const
    {
        irrevocable_change(state, txn, base_fee_per_gas);

        // EIP-3651
        if constexpr (rev >= EVMC_SHANGHAI) {
            host.access_account(beneficiary);
        }

        state.access_account(*txn.from);
        for (auto const &ae : txn.access_list) {
            state.access_account(ae.a);
            for (auto const &keys : ae.keys) {
                state.access_storage(ae.a, keys);
            }
        }
        if (txn.to) {
            state.access_account(*txn.to);
        }

        auto const msg = to_message(txn);
        auto const result = host.call(msg);

        MONAD_DEBUG_ASSERT(result.gas_left >= 0);
        MONAD_DEBUG_ASSERT(result.gas_refund >= 0);
        MONAD_DEBUG_ASSERT(
            txn.gas_limit >= static_cast<uint64_t>(result.gas_left));
        auto const gas_remaining = refund_gas(
            state,
            txn,
            base_fee_per_gas,
            static_cast<uint64_t>(result.gas_left),
            static_cast<uint64_t>(result.gas_refund));
        auto const gas_used = txn.gas_limit - gas_remaining;
        auto const reward =
            calculate_txn_award<rev>(txn, base_fee_per_gas, gas_used);
        state.add_to_balance(beneficiary, reward);

        // finalize state, Eqn. 77-79
        state.destruct_suicides();
        if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
            state.destruct_touched_dead();
        }

        Receipt receipt{
            .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
            .gas_used = gas_used,
            .type = txn.type};
        for (auto &log : state.logs()) {
            receipt.add_log(std::move(log));
        }

        return receipt;
    }

    static constexpr ValidationStatus validate_and_execute(
        Transaction const &tx, BlockHeader const &hdr,
        BlockHashBuffer const &block_hash_buffer, State &state,
        Receipt &receipt)
    {
        MONAD_DEBUG_ASSERT(
            static_validate_txn<rev>(tx, hdr.base_fee_per_gas) ==
            ValidationStatus::SUCCESS);

        TransactionProcessor<rev> processor{};

        if (auto const validity = validate_txn(state, tx);
            validity != ValidationStatus::SUCCESS) {
            // TODO: Issue #164, Issue #54
            return validity;
        }

        auto const tx_context = get_tx_context<rev>(tx, hdr);
        EvmcHost<rev> host{tx_context, block_hash_buffer, state};
        receipt = processor.execute(
            state, host, tx, hdr.base_fee_per_gas.value_or(0), hdr.beneficiary);

        return ValidationStatus::SUCCESS;
    }
};

MONAD_NAMESPACE_END
