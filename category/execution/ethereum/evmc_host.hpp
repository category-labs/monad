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
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/types.hpp>

#include <intx/intx.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <functional>
#include <utility>

MONAD_NAMESPACE_BEGIN

static_assert(sizeof(vm::Host) == 24);
static_assert(alignof(vm::Host) == 8);

class BlockHashBuffer;

class EvmcHostBase : public vm::Host
{
    BlockHashBuffer const &block_hash_buffer_;

protected:
    evmc_tx_context const &tx_context_;
    State &state_;
    CallTracerBase &call_tracer_;
    bool log_native_transfers_;

public:
    EvmcHostBase(
        CallTracerBase &, evmc_tx_context const &, BlockHashBuffer const &,
        State &, bool log_native_transfers) noexcept;

    virtual ~EvmcHostBase() noexcept = default;

    virtual bytes32_t
    get_storage(Address const &, bytes32_t const &key) const noexcept override;

    virtual evmc_storage_status set_storage(
        Address const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;

    virtual evmc::uint256be
    get_balance(Address const &) const noexcept override;

    virtual size_t get_code_size(Address const &) const noexcept override;

    virtual bytes32_t get_code_hash(Address const &) const noexcept override;

    virtual size_t copy_code(
        Address const &, size_t offset, uint8_t *data,
        size_t size) const noexcept override;

    virtual evmc_tx_context const *get_tx_context() const noexcept override;

    virtual bytes32_t get_block_hash(int64_t) const noexcept override;

    virtual void emit_log(
        Address const &, uint8_t const *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) noexcept override;

    virtual evmc_access_status
    access_storage(Address const &, bytes32_t const &key) noexcept override;

    virtual bytes32_t get_transient_storage(
        Address const &, bytes32_t const &key) const noexcept override;

    virtual void set_transient_storage(
        Address const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;
};

static_assert(sizeof(EvmcHostBase) == 64);
static_assert(alignof(EvmcHostBase) == 8);

template <Traits traits>
struct EvmcHost final : public EvmcHostBase
{
    Transaction const &tx_;
    std::optional<uint256_t> base_fee_per_gas_;
    uint64_t i_;
    ChainContext<traits> const &chain_ctx_;

    EvmcHost(
        CallTracerBase &call_tracer, evmc_tx_context const &tx_context,
        BlockHashBuffer const &block_hash_buffer, State &state,
        Transaction const &tx, std::optional<uint256_t> base_fee_per_gas,
        uint64_t i, ChainContext<traits> const &chain_ctx,
        bool const log_native_transfers = false) noexcept
        : EvmcHostBase{call_tracer, tx_context, block_hash_buffer, state, log_native_transfers}
        , tx_{tx}
        , base_fee_per_gas_{base_fee_per_gas}
        , i_{i}
        , chain_ctx_{chain_ctx}
    {
    }

    virtual bool account_exists(Address const &address) const noexcept override
    {
        try {
            if constexpr (traits::evm_rev() < EVMC_SPURIOUS_DRAGON) {
                return state_.account_exists(address);
            }
            return !state_.account_is_dead(address);
        }
        catch (...) {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual bool selfdestruct(
        Address const &address, Address const &beneficiary) noexcept override
    {
        try {
            auto const [result, transferred_balance] =
                state_.selfdestruct<traits>(address, beneficiary);

            call_tracer_.on_self_destruct(
                address, beneficiary, transferred_balance);

            // Skip emitting native transfer events when the beneficiary and
            // destructed contract are the same account (i.e. no net transfer of
            // funds).
            if (result && address != beneficiary) {
                emit_native_transfer_event(
                    address, beneficiary, transferred_balance);
            }

            return result;
        }
        catch (...) {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual evmc::Result call(evmc_message const &msg) noexcept override
    {
        try {
            if (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2) {
                auto result = ::monad::create<traits>(this, state_, msg);

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
                return ::monad::call<traits>(this, state_, msg);
            }
        }
        catch (...) {
            capture_current_exception();
        }
        stack_unwind();
    }

    virtual evmc_access_status
    access_account(Address const &address) noexcept override
    {
        try {
            if (is_precompile<traits>(address)) {
                return EVMC_ACCESS_WARM;
            }
            return state_.access_account(address);
        }
        catch (...) {
            capture_current_exception();
        }
        stack_unwind();
    }

    void transfer_balances(evmc_message const &msg, Address const &to)
    {
        uint256_t const value = intx::be::load<uint256_t>(msg.value);
        state_.subtract_from_balance(msg.sender, value);
        state_.add_to_balance(to, value);

        // Skip self-transfers when emitting native transfer events (those where
        // the sender is also the destination).
        if (msg.sender != to) {
            emit_native_transfer_event(msg.sender, to, value);
        }
    }

    CallTracerBase &get_call_tracer() noexcept
    {
        return call_tracer_;
    }

private:
    void emit_native_transfer_event(
        Address const &from, Address const &to, uint256_t const &value)
    {
        if (log_native_transfers_ && value > 0) {
            static constexpr auto sender =
                0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_address;
            static constexpr auto signature =
                abi_encode_event_signature("Transfer(address,address,uint256)");
            static_assert(
                signature ==
                0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef_bytes32);

            auto event = EventBuilder(sender, signature)
                             .add_topic(abi_encode_address(from))
                             .add_topic(abi_encode_address(to))
                             .add_data(abi_encode_uint(u256_be{value}))
                             .build();

            state_.store_log(event);
            call_tracer_.on_log(std::move(event));
        }
    }
};

static_assert(sizeof(EvmcHost<EvmTraits<EVMC_LATEST_STABLE_REVISION>>) == 128);
static_assert(alignof(EvmcHost<EvmTraits<EVMC_LATEST_STABLE_REVISION>>) == 8);
static_assert(sizeof(EvmcHost<MonadTraits<MONAD_NEXT>>) == 128);
static_assert(alignof(EvmcHost<MonadTraits<MONAD_NEXT>>) == 8);

MONAD_NAMESPACE_END
