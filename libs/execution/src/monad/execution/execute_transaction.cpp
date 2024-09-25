#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/fiber/fiber_semaphore.h>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

// YP Sec 6.2 "irrevocable_change"
template <evmc_revision rev>
constexpr void irrevocable_change(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas)
{
    if (tx.to) { // EVM will increment if new contract
        auto const nonce = state.get_nonce(sender);
        state.set_nonce(sender, nonce + 1);
    }

    auto const upfront_cost =
        tx.gas_limit * gas_price<rev>(tx, base_fee_per_gas);
    state.subtract_from_balance(sender, upfront_cost);
}

// YP Eqn 72
template <evmc_revision rev>
constexpr uint64_t g_star(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    // EIP-3529
    constexpr auto max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
    auto const refund_allowance =
        (tx.gas_limit - gas_remaining) / max_refund_quotient;

    return gas_remaining + std::min(refund_allowance, refund);
}

uint64_t g_star(
    evmc_revision const rev, Transaction const &tx,
    uint64_t const gas_remaining, uint64_t const refund)
{
    SWITCH_EVMC_REVISION(g_star, tx, gas_remaining, refund);
    MONAD_ASSERT(false);
}

template <evmc_revision rev>
constexpr evmc_message to_message(Transaction const &tx, Address const &sender)
{
    auto const to_address = [&tx] {
        if (tx.to) {
            return std::pair{EVMC_CALL, *tx.to};
        }
        return std::pair{EVMC_CREATE, Address{}};
    }();

    evmc_message msg{
        .kind = to_address.first,
        .flags = 0,
        .depth = 0,
        .gas = static_cast<int64_t>(tx.gas_limit - intrinsic_gas<rev>(tx)),
        .recipient = to_address.second,
        .sender = sender,
        .input_data = tx.data.data(),
        .input_size = tx.data.size(),
        .value = {},
        .create2_salt = {},
        .code_address = to_address.second,
        .code = nullptr, // TODO
        .code_size = 0, // TODO
    };
    intx::be::store(msg.value.bytes, tx.value);
    return msg;
}

template <evmc_revision rev>
evmc::Result execute_impl_no_validation(
    State &state, EvmcHost<rev> &host, Transaction const &tx,
    Address const &sender, uint256_t const &base_fee_per_gas,
    Address const &beneficiary, size_t const max_code_size)
{
    irrevocable_change<rev>(state, tx, sender, base_fee_per_gas);

    // EIP-3651
    if constexpr (rev >= EVMC_SHANGHAI) {
        host.access_account(beneficiary);
    }

    state.access_account(sender);
    for (auto const &ae : tx.access_list) {
        state.access_account(ae.a);
        for (auto const &keys : ae.keys) {
            state.access_storage(ae.a, keys);
        }
    }
    if (MONAD_LIKELY(tx.to)) {
        state.access_account(*tx.to);
    }

    auto const msg = to_message<rev>(tx, sender);

    return (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2)
               ? ::monad::create<rev>(&host, state, msg, max_code_size)
               : ::monad::call(&host, state, msg);
}

EXPLICIT_EVMC_REVISION(execute_impl_no_validation);

template <evmc_revision rev>
Receipt execute_final(
    Chain const &chain, State &state, BlockHeader const &header,
    Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas, evmc::Result const &result,
    Address const &beneficiary)
{
    MONAD_ASSERT(result.gas_left >= 0);
    MONAD_ASSERT(result.gas_refund >= 0);
    MONAD_ASSERT(tx.gas_limit >= static_cast<uint64_t>(result.gas_left));

    // refund and priority, Eqn. 73-76
    auto const gas_refund = chain.compute_gas_refund(
        header.number,
        header.timestamp,
        tx,
        static_cast<uint64_t>(result.gas_left),
        static_cast<uint64_t>(result.gas_refund));
    auto const gas_cost = gas_price<rev>(tx, base_fee_per_gas);
    state.add_to_balance(sender, gas_cost * gas_refund);

    auto const gas_used = tx.gas_limit - gas_refund;
    auto const reward =
        calculate_txn_award<rev>(tx, base_fee_per_gas, gas_used);
    state.add_to_balance(beneficiary, reward);

    // finalize state, Eqn. 77-79
    state.destruct_suicides<rev>();
    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    Receipt receipt{
        .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
        .gas_used = gas_used,
        .type = tx.type};
    for (auto const &log : state.logs()) {
        receipt.add_log(std::move(log));
    }

    return receipt;
}

template <evmc_revision rev>
Result<evmc::Result> execute_impl2(
    CallTracerBase &call_tracer, Chain const &chain, Transaction const &tx,
    Address const &sender, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, State &state)
{
    auto const sender_account = state.recent_account(sender);
    BOOST_OUTCOME_TRY(validate_transaction(tx, sender_account));

    size_t const max_code_size =
        chain.get_max_code_size(hdr.number, hdr.timestamp);

    auto const tx_context =
        get_tx_context<rev>(tx, sender, hdr, chain.get_chain_id());
    EvmcHost<rev> host{
        call_tracer, tx_context, block_hash_buffer, state, max_code_size};

    return execute_impl_no_validation<rev>(
        state,
        host,
        tx,
        sender,
        hdr.base_fee_per_gas.value_or(0),
        hdr.beneficiary,
        max_code_size);
}

template <evmc_revision rev>
Result<ExecutionResult> execute_impl(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    Address const &sender, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, BlockState &block_state,
    monad_fiber_semaphore_t *txn_sync_semaphore)
{
    BOOST_OUTCOME_TRY(static_validate_transaction<rev>(
        tx,
        hdr.base_fee_per_gas,
        chain.get_chain_id(),
        chain.get_max_code_size(hdr.number, hdr.timestamp)));

    {
        TRACE_TXN_EVENT(StartExecution);

        State state{block_state, Incarnation{hdr.number, i + 1}};
        state.set_original_nonce(sender, tx.nonce);

#ifdef ENABLE_CALL_TRACING
        CallTracer call_tracer{tx};
#else
        NoopCallTracer call_tracer{};
#endif

        auto result = execute_impl2<rev>(
            call_tracer, chain, tx, sender, hdr, block_hash_buffer, state);

        {
            TRACE_TXN_EVENT(StartStall);
            // Ensure previous transaction is fully merged first
            monad_fiber_semaphore_acquire(
                txn_sync_semaphore, MONAD_FIBER_PRIO_NO_CHANGE);
        }

        if (block_state.can_merge(state)) {
            if (result.has_error()) {
                return std::move(result.error());
            }
            auto const receipt = execute_final<rev>(
                chain,
                state,
                hdr,
                tx,
                sender,
                hdr.base_fee_per_gas.value_or(0),
                result.value(),
                hdr.beneficiary);
            call_tracer.on_receipt(receipt);
            block_state.merge(state);

            auto const frames = call_tracer.get_frames();
            return ExecutionResult{
                .receipt = receipt,
                .sender = sender,
                .call_frames = {frames.begin(), frames.end()}};
        }
    }
    {
        TRACE_TXN_EVENT(StartRetry);

        State state{block_state, Incarnation{hdr.number, i + 1}};

#ifdef ENABLE_CALL_TRACING
        CallTracer call_tracer{tx};
#else
        NoopCallTracer call_tracer{};
#endif

        auto result = execute_impl2<rev>(
            call_tracer, chain, tx, sender, hdr, block_hash_buffer, state);

        MONAD_ASSERT(block_state.can_merge(state));
        if (result.has_error()) {
            return std::move(result.error());
        }
        auto const receipt = execute_final<rev>(
            chain,
            state,
            hdr,
            tx,
            sender,
            hdr.base_fee_per_gas.value_or(0),
            result.value(),
            hdr.beneficiary);
        call_tracer.on_receipt(receipt);
        block_state.merge(state);

        auto const frames = call_tracer.get_frames();
        return ExecutionResult{
            .receipt = receipt,
            .sender = sender,
            .call_frames = {frames.begin(), frames.end()}};
    }
}

EXPLICIT_EVMC_REVISION(execute_impl);

template <evmc_revision rev>
Result<ExecutionResult> execute(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    std::optional<Address> const &sender, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, BlockState &block_state,
    monad_fiber_semaphore_t *sender_semaphore,
    monad_fiber_semaphore_t *txn_sync_semaphore)
{
    TRACE_TXN_EVENT(StartTxn);

    // Wait for the sender to materialize
    monad_fiber_semaphore_acquire(sender_semaphore, MONAD_FIBER_PRIO_NO_CHANGE);
    if (MONAD_UNLIKELY(!sender.has_value())) {
        return TransactionError::MissingSender;
    }

    return execute_impl<rev>(
        chain,
        i,
        tx,
        sender.value(),
        hdr,
        block_hash_buffer,
        block_state,
        txn_sync_semaphore);
}

EXPLICIT_EVMC_REVISION(execute);

MONAD_NAMESPACE_END
