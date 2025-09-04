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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

EvmcHostBase::EvmcHostBase(
    Chain const &chain, CallTracerBase &call_tracer,
    evmc_tx_context const &tx_context, BlockHashBuffer const &block_hash_buffer,
    State &state, size_t const max_code_size, size_t const max_initcode_size,
    std::function<bool()> const &revert_transaction) noexcept
    : block_hash_buffer_{block_hash_buffer}
    , tx_context_{tx_context}
    , chain_{chain}
    , state_{state}
    , call_tracer_{call_tracer}
    , max_code_size_{max_code_size}
    , max_initcode_size_{max_initcode_size}
    , revert_transaction_{revert_transaction}
{
}

bytes32_t EvmcHostBase::get_storage(
    Address const &address, bytes32_t const &key) const noexcept
{
    try {
        return state_.get_storage(address, key);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

evmc_storage_status EvmcHostBase::set_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    try {
        return state_.set_storage(address, key, value);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

evmc::uint256be EvmcHostBase::get_balance(Address const &address) const noexcept
{
    try {
        return state_.get_balance(address);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

size_t EvmcHostBase::get_code_size(Address const &address) const noexcept
{
    try {
        return state_.get_code_size(address);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

bytes32_t EvmcHostBase::get_code_hash(Address const &address) const noexcept
{
    try {
        if (state_.account_is_dead(address)) {
            return bytes32_t{};
        }
        return state_.get_code_hash(address);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

size_t EvmcHostBase::copy_code(
    Address const &address, size_t offset, uint8_t *data,
    size_t size) const noexcept
{
    try {
        return state_.copy_code(address, offset, data, size);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

evmc_tx_context EvmcHostBase::get_tx_context() const noexcept
{
    return tx_context_;
}

bytes32_t
EvmcHostBase::get_block_hash(int64_t const block_number) const noexcept
{
    try {
        MONAD_ASSERT(block_number >= 0);
        return block_hash_buffer_.get(static_cast<uint64_t>(block_number));
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

void EvmcHostBase::emit_log(
    Address const &address, uint8_t const *data, size_t data_size,
    bytes32_t const topics[], size_t num_topics) noexcept
{
    try {
        Receipt::Log log{.data = {data, data_size}, .address = address};
        for (auto i = 0u; i < num_topics; ++i) {
            log.topics.push_back({topics[i]});
        }
        state_.store_log(std::move(log));
        return;
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

evmc_access_status EvmcHostBase::access_storage(
    Address const &address, bytes32_t const &key) noexcept
{
    try {
        return state_.access_storage(address, key);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

bytes32_t EvmcHostBase::get_transient_storage(
    Address const &address, bytes32_t const &key) const noexcept
{
    try {
        return state_.get_transient_storage(address, key);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

void EvmcHostBase::set_transient_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    try {
        return state_.set_transient_storage(address, key, value);
    }
    catch (...) {
        capture_current_exception();
    }
    stack_unwind();
}

MONAD_NAMESPACE_END
