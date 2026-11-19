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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/native_transfer_log.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/types.hpp>

#include <functional>
#include <utility>

MONAD_NAMESPACE_BEGIN

static_assert(sizeof(vm::Host) == 24);
static_assert(alignof(vm::Host) == 8);

class BlockHashBuffer;

class StateHostBase : public vm::Host
{
    BlockHashBuffer const &block_hash_buffer_;

protected:
    vm::TxContext const &tx_context_;
    State &state_;
    CallTracerBase &call_tracer_;

public:
    bool const log_native_transfers_;
    trace::StateTracer &state_tracer_;

    StateHostBase(
        CallTracerBase &, trace::StateTracer &, vm::TxContext const &,
        BlockHashBuffer const &, State &, bool log_native_transfers) noexcept;

    virtual ~StateHostBase() noexcept = default;

    virtual vm::TxContext const *get_tx_context() const noexcept override;

private:
    virtual bytes32_t
    get_storage_impl(Address const &, bytes32_t const &key) const override;

    virtual StorageStatus set_storage_impl(
        Address const &, bytes32_t const &key, bytes32_t const &value) override;

    virtual uint256_t get_balance_impl(Address const &) const override;

    virtual size_t get_code_size_impl(Address const &) const override;

    virtual bytes32_t get_code_hash_impl(Address const &) const override;

    virtual size_t copy_code_impl(
        Address const &, size_t offset, uint8_t *data,
        size_t size) const override;

    virtual bytes32_t get_block_hash_impl(int64_t) const override;

    virtual void emit_log_impl(
        Address const &, uint8_t const *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) override;

    virtual bytes32_t get_transient_storage_impl(
        Address const &, bytes32_t const &key) const override;

    virtual void set_transient_storage_impl(
        Address const &, bytes32_t const &key, bytes32_t const &value) override;
};

static_assert(sizeof(StateHostBase) == 72);
static_assert(alignof(StateHostBase) == 8);

template <Traits traits>
struct StateHost final : public StateHostBase
{
    Transaction const &tx_;
    std::optional<uint256_t> base_fee_per_gas_;
    uint64_t i_;
    ChainContext<traits> const &chain_ctx_;

    StateHost(
        CallTracerBase &call_tracer, trace::StateTracer &state_tracer,
        vm::TxContext const &tx_context,
        BlockHashBuffer const &block_hash_buffer, State &state,
        Transaction const &tx, std::optional<uint256_t> const base_fee_per_gas,
        uint64_t const i, ChainContext<traits> const &chain_ctx,
        bool const log_native_transfers = false) noexcept
        : StateHostBase{call_tracer, state_tracer, tx_context, block_hash_buffer, state, log_native_transfers}
        , tx_{tx}
        , base_fee_per_gas_{base_fee_per_gas}
        , i_{i}
        , chain_ctx_{chain_ctx}
    {
    }

    StateHost(
        CallTracerBase &, trace::StateTracer &, vm::TxContext const &,
        BlockHashBuffer const &, State &, Transaction const &,
        std::optional<uint256_t>, uint64_t, ChainContext<traits> const &&,
        bool = false) = delete;

    CallTracerBase &get_call_tracer() noexcept
    {
        return call_tracer_;
    }

private:
    virtual bool account_exists_impl(Address const &address) const override
    {
        static_assert(traits::evm_rev() >= EvmRevision::SpuriousDragon);

        return !state_.account_is_dead(address);
    }

    virtual bool selfdestruct_impl(
        Address const &address, Address const &beneficiary) override
    {
        auto const [result, transferred_balance] =
            state_.selfdestruct<traits>(address, beneficiary);

        call_tracer_.on_self_destruct(
            address, beneficiary, transferred_balance);

        emit_native_transfer_logs<traits>(
            state_,
            call_tracer_,
            address,
            beneficiary,
            transferred_balance,
            log_native_transfers_);

        return result;
    }

    virtual vm::Result call_impl(vm::Message const &msg) override
    {
        if (msg.kind == vm::CallKind::Create ||
            msg.kind == vm::CallKind::Create2) {
            auto result =
                ::monad::execute_create_message<traits>(this, state_, msg);

            // EIP-211
            if (result.status_code != CallStatus::Revert) {
                result = vm::Result{
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

    virtual AccessStatus access_account_impl(Address const &address) override
    {
        if (is_precompile<traits>(address)) {
            return AccessStatus::Warm;
        }
        return state_.access_account(address);
    }

    virtual AccessStatus
    access_storage_impl(Address const &address, bytes32_t const &key) override
    {
        return state_.access_storage<traits>(address, key);
    }

    virtual PageStorageStatus update_page_impl(
        Address const &address, bytes32_t const &key,
        StorageStatus const status) override
    {
        if constexpr (traits::mip_8_active()) {
            return state_.update_page(address, key, status);
        }
        else {
            MONAD_ABORT("update_page is MIP-8 only");
        }
    }
};

static_assert(sizeof(StateHost<EvmTraits<EvmRevision::LatestStable>>) == 136);
static_assert(alignof(StateHost<EvmTraits<EvmRevision::LatestStable>>) == 8);
static_assert(sizeof(StateHost<MonadTraits<MONAD_NEXT>>) == 136);
static_assert(alignof(StateHost<MonadTraits<MONAD_NEXT>>) == 8);

MONAD_NAMESPACE_END
