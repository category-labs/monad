// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/throw.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <functional>
#include <utility>

MONAD_NAMESPACE_BEGIN

static_assert(sizeof(vm::Host) == 24);
static_assert(alignof(vm::Host) == 8);

class BlockHashBuffer;

// Sender for the EIP-7002/EIP-7251 system calls; emitter for EIP-7708's logs.
inline constexpr Address SYSTEM_ADDRESS =
    0xfffffffffffffffffffffffffffffffffffffffe_address;

// ERC-7528 pseudo-address: eth_simulate's traceTransfers emitter, any revision.
inline constexpr Address SIMULATE_NATIVE_TOKEN_LOG_ADDRESS =
    0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_address;

class EvmcHostBase : public vm::Host
{
    BlockHashBuffer const &block_hash_buffer_;

protected:
    evmc_tx_context const &tx_context_;
    State &state_;
    CallTracerBase &call_tracer_;
    bool const log_native_transfers_;

public:
    trace::StateTracer &state_tracer_;

    EvmcHostBase(
        CallTracerBase &, trace::StateTracer &, evmc_tx_context const &,
        BlockHashBuffer const &, State &, bool log_native_transfers) noexcept;

    virtual ~EvmcHostBase() noexcept = default;

    virtual evmc::bytes32 get_storage(
        evmc::address const &,
        evmc::bytes32 const &key) const noexcept override;

    virtual evmc_storage_status set_storage(
        evmc::address const &, evmc::bytes32 const &key,
        evmc::bytes32 const &value) noexcept override;

    virtual evmc::uint256be
    get_balance(evmc::address const &) const noexcept override;

    virtual size_t get_code_size(evmc::address const &) const noexcept override;

    virtual evmc::bytes32
    get_code_hash(evmc::address const &) const noexcept override;

    virtual size_t copy_code(
        evmc::address const &, size_t offset, uint8_t *data,
        size_t size) const noexcept override;

    virtual evmc_tx_context const *get_tx_context() const noexcept override;

    virtual evmc::bytes32 get_block_hash(int64_t) const noexcept override;

    virtual void emit_log(
        evmc::address const &, uint8_t const *data, size_t data_size,
        evmc::bytes32 const topics[], size_t num_topics) noexcept override;

    virtual evmc::bytes32 get_transient_storage(
        evmc::address const &,
        evmc::bytes32 const &key) const noexcept override;

    virtual void set_transient_storage(
        evmc::address const &, evmc::bytes32 const &key,
        evmc::bytes32 const &value) noexcept override;

    virtual PageStorageStatus update_page(
        evmc::address const &, evmc::bytes32 const &page_key,
        evmc_storage_status) noexcept override;
};

static_assert(sizeof(EvmcHostBase) == 72);
static_assert(alignof(EvmcHostBase) == 8);

template <Traits traits>
struct EvmcHost final : public EvmcHostBase
{
    Transaction const &tx_;
    std::optional<uint256_t> base_fee_per_gas_;
    uint64_t i_;
    ChainContext<traits> const &chain_ctx_;

    EvmcHost(
        CallTracerBase &call_tracer, trace::StateTracer &state_tracer,
        evmc_tx_context const &tx_context,
        BlockHashBuffer const &block_hash_buffer, State &state,
        Transaction const &tx, std::optional<uint256_t> const base_fee_per_gas,
        uint64_t const i, ChainContext<traits> const &chain_ctx,
        bool const log_native_transfers = false) noexcept
        : EvmcHostBase{call_tracer, state_tracer, tx_context, block_hash_buffer, state, log_native_transfers}
        , tx_{tx}
        , base_fee_per_gas_{base_fee_per_gas}
        , i_{i}
        , chain_ctx_{chain_ctx}
    {
    }

    virtual bool
    account_exists(evmc::address const &address) const noexcept override
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);

        MONAD_TRY
        {
            return !state_.account_is_dead(address);
        }
        MONAD_CATCH(...)
        {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual bool selfdestruct(
        evmc::address const &address,
        evmc::address const &beneficiary) noexcept override
    {
        MONAD_TRY
        {
            auto const [result, transferred_balance] =
                state_.selfdestruct<traits>(address, beneficiary);

            call_tracer_.on_self_destruct(
                address, beneficiary, transferred_balance);

            emit_native_transfer_event(
                address, beneficiary, transferred_balance);

            return result;
        }
        MONAD_CATCH(...)
        {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual evmc::Result call(evmc_message const &msg) noexcept override
    {
        MONAD_TRY
        {
            if (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2) {
                auto result =
                    ::monad::execute_create_message<traits>(this, state_, msg);

                // EIP-211
                if (result.status_code != EVMC_REVERT) {
                    result = evmc::Result{
                        result.status_code,
                        result.gas_left,
                        result.gas_refund,
                        result.create_address};
                }
                return result;
            }
            else {
                return ::monad::execute_call_message<traits>(this, state_, msg);
            }
        }
        MONAD_CATCH(...)
        {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual evmc_access_status
    access_account(evmc::address const &address) noexcept override
    {
        MONAD_TRY
        {
            if (is_precompile<traits>(address)) {
                return EVMC_ACCESS_WARM;
            }
            return state_.access_account(address);
        }
        MONAD_CATCH(...)
        {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual evmc_access_status access_storage(
        evmc::address const &address,
        evmc::bytes32 const &key) noexcept override
    {
        MONAD_TRY
        {
            return state_.access_storage<traits>(address, key);
        }
        MONAD_CATCH(...)
        {
            capture_current_exception();
        }
        stack_unwind();
    }

    CallTracerBase &get_call_tracer() noexcept
    {
        return call_tracer_;
    }

    // Not every ETH movement emits. The EIP excludes withdrawals (not attached
    // to a transaction, so no natural emission point), priority fees and the
    // base-fee burn (derivable from the header). Beyond the EIP, monad's
    // staking contract moves, mints and burns ETH by direct balance mutation
    // rather than a value transfer, so none of that emits either.
    void emit_native_transfer_event(
        Address const &from, Address const &to, uint256_t const &value)
    {
        // Pre-activation nothing is emitted unless eth_simulate asked for it,
        // so short-circuit on the flag before comparing value and addresses.
        if constexpr (!traits::eip_7708_active()) {
            if (MONAD_LIKELY(!log_native_transfers_)) {
                return;
            }
        }

        // Skip when no value moves, or from == to so there is no net transfer.
        // EIP-7708 words its cases the same way: nonzero-value-transferring, to
        // a different account. One predicate serves both log kinds below.
        // Most messages carry no value, so this is the common exit; the hint
        // keeps the event-building below off the per-message path.
        if (MONAD_LIKELY(value == 0 || from == to)) {
            return;
        }

        static constexpr bytes32_t signature =
            abi_encode_event_signature("Transfer(address,address,uint256)");
        static_assert(
            signature ==
            bytes32_from_hex("ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a"
                             "11628f55a4df523b3ef"));

        auto const emit = [&](Address const &log_address) {
            auto event = EventBuilder(log_address, signature)
                             .add_topic(abi_encode_address(from))
                             .add_topic(abi_encode_address(to))
                             .add_data(abi_encode_uint(u256_be{value}))
                             .build();

            state_.store_log(event);
            call_tracer_.on_log(std::move(event));
        };

        // Consensus artifact, so not conditioned on log_native_transfers_.
        if constexpr (traits::eip_7708_active()) {
            emit(SYSTEM_ADDRESS);
        }

        // eth_simulate's ERC-7528 synthetic, emitted alongside the consensus
        // log rather than replaced by it -- geth returns both. Emitted second
        // so the two stay in execution order; note that logIndex counts both,
        // so a consumer dropping the 0xeeee... entries sees only even indices.
        if (log_native_transfers_) {
            emit(SIMULATE_NATIVE_TOKEN_LOG_ADDRESS);
        }
    }
};

static_assert(
    sizeof(EvmcHost<EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>>) == 136);
static_assert(
    alignof(EvmcHost<EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>>) == 8);
static_assert(sizeof(EvmcHost<MonadTraits<MONAD_NEXT>>) == 136);
static_assert(alignof(EvmcHost<MonadTraits<MONAD_NEXT>>) == 8);

MONAD_NAMESPACE_END
