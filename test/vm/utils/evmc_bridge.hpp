// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/tx_context.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <bit>
#include <utility>

// Conversions between the in-tree VM types and evmc's C ABI. The OCaml spec
// VM is the only remaining evmc consumer, so these live with the test utils.
namespace monad::vm::test
{
#define MONAD_ASSERT_ENUM_EQ(monad_value, evmc_value)                          \
    static_assert(                                                             \
        static_cast<long long>(std::to_underlying(monad_value)) ==             \
        static_cast<long long>(std::to_underlying(evmc_value)))

    MONAD_ASSERT_ENUM_EQ(AccessStatus::Cold, EVMC_ACCESS_COLD);
    MONAD_ASSERT_ENUM_EQ(AccessStatus::Warm, EVMC_ACCESS_WARM);

    MONAD_ASSERT_ENUM_EQ(StorageStatus::Assigned, EVMC_STORAGE_ASSIGNED);
    MONAD_ASSERT_ENUM_EQ(StorageStatus::Added, EVMC_STORAGE_ADDED);
    MONAD_ASSERT_ENUM_EQ(StorageStatus::Deleted, EVMC_STORAGE_DELETED);
    MONAD_ASSERT_ENUM_EQ(StorageStatus::Modified, EVMC_STORAGE_MODIFIED);
    MONAD_ASSERT_ENUM_EQ(
        StorageStatus::DeletedAdded, EVMC_STORAGE_DELETED_ADDED);
    MONAD_ASSERT_ENUM_EQ(
        StorageStatus::ModifiedDeleted, EVMC_STORAGE_MODIFIED_DELETED);
    MONAD_ASSERT_ENUM_EQ(
        StorageStatus::DeletedRestored, EVMC_STORAGE_DELETED_RESTORED);
    MONAD_ASSERT_ENUM_EQ(
        StorageStatus::AddedDeleted, EVMC_STORAGE_ADDED_DELETED);
    MONAD_ASSERT_ENUM_EQ(
        StorageStatus::ModifiedRestored, EVMC_STORAGE_MODIFIED_RESTORED);

    MONAD_ASSERT_ENUM_EQ(CallStatus::Success, EVMC_SUCCESS);
    MONAD_ASSERT_ENUM_EQ(CallStatus::Failure, EVMC_FAILURE);
    MONAD_ASSERT_ENUM_EQ(CallStatus::Revert, EVMC_REVERT);
    MONAD_ASSERT_ENUM_EQ(CallStatus::OutOfGas, EVMC_OUT_OF_GAS);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::InvalidInstruction, EVMC_INVALID_INSTRUCTION);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::UndefinedInstruction, EVMC_UNDEFINED_INSTRUCTION);
    MONAD_ASSERT_ENUM_EQ(CallStatus::StackOverflow, EVMC_STACK_OVERFLOW);
    MONAD_ASSERT_ENUM_EQ(CallStatus::StackUnderflow, EVMC_STACK_UNDERFLOW);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::BadJumpDestination, EVMC_BAD_JUMP_DESTINATION);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::InvalidMemoryAccess, EVMC_INVALID_MEMORY_ACCESS);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::CallDepthExceeded, EVMC_CALL_DEPTH_EXCEEDED);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::StaticModeViolation, EVMC_STATIC_MODE_VIOLATION);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::PrecompileFailure, EVMC_PRECOMPILE_FAILURE);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::ContractValidationFailure,
        EVMC_CONTRACT_VALIDATION_FAILURE);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::ArgumentOutOfRange, EVMC_ARGUMENT_OUT_OF_RANGE);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::InsufficientBalance, EVMC_INSUFFICIENT_BALANCE);
    MONAD_ASSERT_ENUM_EQ(
        CallStatus::ReserveBalanceViolation,
        EVMC_MONAD_RESERVE_BALANCE_VIOLATION);
    MONAD_ASSERT_ENUM_EQ(CallStatus::InternalError, EVMC_INTERNAL_ERROR);
    MONAD_ASSERT_ENUM_EQ(CallStatus::Rejected, EVMC_REJECTED);
    MONAD_ASSERT_ENUM_EQ(CallStatus::OutOfMemory, EVMC_OUT_OF_MEMORY);

    MONAD_ASSERT_ENUM_EQ(MONAD_ETH_FRONTIER, EVMC_FRONTIER);
    MONAD_ASSERT_ENUM_EQ(MONAD_ETH_OSAKA, EVMC_OSAKA);

    MONAD_ASSERT_ENUM_EQ(CallKind::Call, EVMC_CALL);
    MONAD_ASSERT_ENUM_EQ(CallKind::DelegateCall, EVMC_DELEGATECALL);
    MONAD_ASSERT_ENUM_EQ(CallKind::CallCode, EVMC_CALLCODE);
    MONAD_ASSERT_ENUM_EQ(CallKind::Create, EVMC_CREATE);
    MONAD_ASSERT_ENUM_EQ(CallKind::Create2, EVMC_CREATE2);
    MONAD_ASSERT_ENUM_EQ(CallFlags::Static, EVMC_STATIC);
    MONAD_ASSERT_ENUM_EQ(CallFlags::Delegated, EVMC_DELEGATED);

#undef MONAD_ASSERT_ENUM_EQ

    inline evmc::address to_evmc(Address const &a) noexcept
    {
        return std::bit_cast<evmc::address>(a);
    }

    inline Address from_evmc(evmc_address const &a) noexcept
    {
        return std::bit_cast<Address>(a);
    }

    inline evmc::bytes32 to_evmc(bytes32_t const &b) noexcept
    {
        return std::bit_cast<evmc::bytes32>(b);
    }

    inline bytes32_t from_evmc(evmc_bytes32 const &b) noexcept
    {
        return std::bit_cast<bytes32_t>(b);
    }

    inline evmc_access_status
    to_evmc_access_status(AccessStatus const s) noexcept
    {
        return static_cast<evmc_access_status>(std::to_underlying(s));
    }

    inline evmc_storage_status
    to_evmc_storage_status(StorageStatus const s) noexcept
    {
        return static_cast<evmc_storage_status>(std::to_underlying(s));
    }

    inline StorageStatus
    from_evmc_storage_status(evmc_storage_status const s) noexcept
    {
        return static_cast<StorageStatus>(std::to_underlying(s));
    }

    inline evmc_page_storage_status
    to_evmc_page_storage_status(PageStorageStatus const s) noexcept
    {
        return {
            .first_page_write = s.first_page_write, .grew_state = s.grew_state};
    }

    inline evmc_status_code to_evmc_status_code(CallStatus const c)
    {
        return static_cast<evmc_status_code>(std::to_underlying(c));
    }

    inline CallStatus from_evmc_status_code(evmc_status_code const c)
    {
        return static_cast<CallStatus>(std::to_underlying(c));
    }

    // Amsterdam and later have no evmc counterpart.
    inline evmc_revision to_evmc_revision(monad_eth_revision const rev)
    {
        MONAD_ASSERT(std::to_underlying(rev) <= std::to_underlying(EVMC_OSAKA));
        return static_cast<evmc_revision>(std::to_underlying(rev));
    }

    inline monad_eth_revision from_evmc_revision(evmc_revision const rev)
    {
        MONAD_ASSERT(rev <= EVMC_OSAKA);
        return static_cast<monad_eth_revision>(std::to_underlying(rev));
    }

    inline Message from_evmc(evmc_message const &m) noexcept
    {
        return Message{
            .kind = static_cast<CallKind>(m.kind),
            .flags = m.flags,
            .depth = m.depth,
            .gas = m.gas,
            .recipient = from_evmc(m.recipient),
            .sender = from_evmc(m.sender),
            .input_data = m.input_data,
            .input_size = m.input_size,
            .value = from_evmc(m.value),
            .create2_salt = from_evmc(m.create2_salt),
            .code_address = from_evmc(m.code_address),
            .memory_handle = m.memory_handle,
            .memory = m.memory,
            .memory_capacity = m.memory_capacity,
        };
    }

    inline evmc_message to_evmc(Message const &m) noexcept
    {
        return evmc_message{
            .kind = static_cast<evmc_call_kind>(m.kind),
            .flags = m.flags,
            .depth = m.depth,
            .gas = m.gas,
            .recipient = to_evmc(m.recipient),
            .sender = to_evmc(m.sender),
            .input_data = m.input_data,
            .input_size = m.input_size,
            .value = to_evmc(m.value),
            .create2_salt = to_evmc(m.create2_salt),
            .code_address = to_evmc(m.code_address),
            .memory_handle = m.memory_handle,
            .memory = m.memory,
            .memory_capacity = m.memory_capacity,
        };
    }

    inline evmc_tx_context to_evmc(TxContext const &c) noexcept
    {
        return evmc_tx_context{
            .tx_gas_price = to_evmc(c.tx_gas_price),
            .tx_origin = to_evmc(c.tx_origin),
            .block_coinbase = to_evmc(c.block_coinbase),
            .block_number = c.block_number,
            .block_timestamp = c.block_timestamp,
            .block_gas_limit = c.block_gas_limit,
            .block_prev_randao = to_evmc(c.block_prev_randao),
            .chain_id = to_evmc(c.chain_id),
            .block_base_fee = to_evmc(c.block_base_fee),
            .blob_base_fee = to_evmc(c.blob_base_fee),
            .blob_hashes =
                reinterpret_cast<evmc_bytes32 const *>(c.blob_hashes),
            .blob_hashes_count = c.blob_hashes_count,
            .initcodes = nullptr,
            .initcodes_count = 0,
            .block_round = c.block_round,
        };
    }
}
