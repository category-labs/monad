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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/tx_context.hpp>

#include <cstddef>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

StateHostBase::StateHostBase(
    CallTracerBase &call_tracer, trace::StateTracer &state_tracer,
    vm::TxContext const &tx_context, BlockHashBuffer const &block_hash_buffer,
    State &state, bool const log_native_transfers) noexcept
    : block_hash_buffer_{block_hash_buffer}
    , tx_context_{tx_context}
    , state_{state}
    , call_tracer_{call_tracer}
    , log_native_transfers_{log_native_transfers}
    , state_tracer_{state_tracer}
{
}

bytes32_t StateHostBase::get_storage_impl(
    Address const &address, bytes32_t const &key) const
{
    return state_.get_storage(address, key);
}

StorageStatus StateHostBase::set_storage_impl(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    return state_.set_storage(address, key, value);
}

uint256_t StateHostBase::get_balance_impl(Address const &address) const
{
    return state_.get_balance(address);
}

size_t StateHostBase::get_code_size_impl(Address const &address) const
{
    if (MONAD_UNLIKELY(trace::is_code_tracer(state_tracer_))) {
        bytes32_t const hash = state_.get_code_hash(address);
        if (hash == NULL_HASH) {
            return 0;
        }
        auto const vcode = state_.read_code(hash);
        MONAD_ASSERT(vcode);
        trace::on_read_code(state_tracer_, hash, vcode->intercode());
        return vcode->intercode()->size();
    }
    return state_.get_code_size(address);
}

bytes32_t StateHostBase::get_code_hash_impl(Address const &address) const
{
    if (state_.account_is_dead(address)) {
        return bytes32_t{};
    }
    return state_.get_code_hash(address);
}

size_t StateHostBase::copy_code_impl(
    Address const &address, size_t const offset, uint8_t *const data,
    size_t const size) const
{
    if (MONAD_UNLIKELY(trace::is_code_tracer(state_tracer_))) {
        bytes32_t const hash = state_.get_code_hash(address);
        if (hash != NULL_HASH) {
            auto const vcode = state_.read_code(hash);
            MONAD_ASSERT(vcode);
            trace::on_read_code(state_tracer_, hash, vcode->intercode());
            return vcode->intercode()->copy_code(offset, data, size);
        }
        return 0;
    }
    return state_.copy_code(address, offset, data, size);
}

vm::TxContext const *StateHostBase::get_tx_context() const noexcept
{
    return &tx_context_;
}

// This attempts to read from the contract first before falling back to the
// block hash buffer. This is currently only called by the BLOCKHASH
// implementation which guarantees that the block_number is in range.
bytes32_t StateHostBase::get_block_hash_impl(int64_t const block_number) const
{
    MONAD_ASSERT(block_number >= 0);
    if (bytes32_t const block_hash =
            get_block_hash_history(state_, static_cast<uint64_t>(block_number));
        block_hash != bytes32_t{}) {
        return block_hash;
    }
    bytes32_t const block_hash =
        block_hash_buffer_.get(static_cast<uint64_t>(block_number));
    MONAD_ASSERT(block_hash != bytes32_t{});
    return block_hash;
}

void StateHostBase::emit_log_impl(
    Address const &address, uint8_t const *const data, size_t const data_size,
    bytes32_t const topics[], size_t const num_topics)
{
    Receipt::Log log{.data = {data, data_size}, .address = address};
    for (auto i = 0u; i < num_topics; ++i) {
        log.topics.emplace_back(topics[i]);
    }
    state_.store_log(log);
    call_tracer_.on_log(std::move(log));
}

bytes32_t StateHostBase::get_transient_storage_impl(
    Address const &address, bytes32_t const &key) const
{
    return state_.get_transient_storage(address, key);
}

void StateHostBase::set_transient_storage_impl(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    return state_.set_transient_storage(address, key, value);
}

MONAD_NAMESPACE_END
