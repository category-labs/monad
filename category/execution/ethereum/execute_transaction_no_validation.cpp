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

#include <category/execution/ethereum/execute_transaction.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/memory_pool.hpp>

#include <cstdint>
#include <limits>
#include <optional>
#include <span>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// YP Sec 6.2 "irrevocable_change"
template <Traits traits>
constexpr void irrevocable_change(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas, uint64_t const excess_blob_gas,
    BlobSchedule const &blob_schedule)
{
    if (tx.to) { // EVM will increment if new contract
        auto const nonce = state.get_nonce(sender);
        state.set_nonce(sender, nonce + 1);
    }

    uint256_t blob_gas = 0;
    if constexpr (traits::eip_4844_active()) {
        blob_gas = (tx.type == TransactionType::eip4844)
                       ? calc_blob_fee(tx, excess_blob_gas, blob_schedule)
                       : 0;
    }
    auto const upfront_cost =
        tx.gas_limit * gas_price<traits>(tx, base_fee_per_gas);
    state.subtract_from_balance(sender, upfront_cost + blob_gas);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
ExecuteTransactionNoValidation<traits>::ExecuteTransactionNoValidation(
    Chain const &chain, Transaction const &tx, Address const &sender,
    std::span<std::optional<Address> const> const authorities,
    BlockHeader const &header)
    : chain_{chain}
    , tx_{tx}
    , sender_{sender}
    , authorities_{authorities}
    , header_{header}
{
}

// EIP-7702
template <Traits traits>
uint64_t ExecuteTransactionNoValidation<traits>::process_authorizations(
    State &state, StateHost<traits> &host)
{

    MONAD_ASSERT(authorities_.size() == tx_.authorization_list.size());

    uint64_t refund = 0u;

    for (auto i = 0u; i < tx_.authorization_list.size(); ++i) {
        auto const &auth_entry = tx_.authorization_list[i];
        MONAD_ASSERT(auth_entry.sc.chain_id.has_value());

        // 1. Verify the chain ID is 0 or the ID of the current chain.
        auto const &chain_id = *auth_entry.sc.chain_id;
        auto const host_chain_id =
            load_be<uint256_t>(host.get_tx_context()->chain_id);

        if (!(chain_id == 0 || chain_id == host_chain_id)) {
            continue;
        }

        // 2. Verify the nonce is less than 2**64 - 1.
        if (auth_entry.nonce == std::numeric_limits<uint64_t>::max()) {
            continue;
        }

        // 3. Let authority = ecrecover(msg, y_parity, r, s).
        auto const &authority = authorities_[i];
        if (!authority.has_value()) {
            continue;
        }

        // Safety: if an authority has a value here, it must have been produced
        // by `recover_authority`, which rejects signatures that are not EIP-2
        // compliant. It is an invariant that non-nullopt auth entries have
        // signatures with lower-half s components.
        MONAD_ASSERT(!auth_entry.sc.signature.has_upper_s());

        // 4. Add authority to accessed_addresses, as defined in EIP-2929.
        state.access_account(*authority);

        // 5. Verify the code of authority is empty or already delegated.
        auto const code_hash = state.get_code_hash(*authority);
        auto const icode = state.read_code(code_hash)->intercode();
        trace::on_read_code(host.state_tracer_, code_hash, icode);
        auto const code = std::span{icode->code(), *icode->code_size()};
        if (!(code.empty() || vm::evm::is_delegated(code))) {
            continue;
        }

        // 6. Verify the nonce of authority is equal to nonce.
        auto const auth_nonce = state.get_nonce(*authority);
        if (auth_entry.nonce != auth_nonce) {
            continue;
        }

        if (!state.account_exists(*authority)) {
            // The authority processing step is happening before the transaction
            // runs, and so we need to create the account such that it cannot be
            // selfdestructed, even if the delegated code runs a `SELFDESTRUCT`
            // opcode. This is not documented explicitly in EIP-7702, but is a
            // consequence of the Cancun selfdestruct rules, and the fact that
            // authority processing (and therefore this account creation) are
            // not part of any transaction.
            state.create_account_no_rollback(*authority);
        }

        // 7. Add PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST gas to the global
        // refund counter if authority is not empty.
        if (!state.account_is_dead(*authority)) {
            refund += (25'000u - 12'500u);
        }

        // 8. Set the code of authority to be 0xef0100 || address. This is a
        // delegation indicator.
        if (auth_entry.address) {
            auto const new_code =
                byte_string(vm::evm::delegation_indicator_prefix()) +
                byte_string(
                    auth_entry.address.bytes, auth_entry.address.bytes + 20);
            state.set_code(*authority, new_code);
        }
        else {
            // If address is 0x0000000000000000000000000000000000000000, do not
            // write the delegation indicator. Clear the account’s code
            state.set_code(*authority, {});
        }

        // 9. Increase the nonce of authority by one.
        state.set_nonce(*authority, auth_nonce + 1);
    }

    return refund;
}

template <Traits traits>
vm::Message ExecuteTransactionNoValidation<traits>::to_message(
    vm::MemoryPool::Ref &msg_memory, uint32_t const msg_memory_capacity) const
{
    auto const to_address = [this] {
        if (tx_.to) {
            return std::pair{vm::CallKind::Call, *tx_.to};
        }
        return std::pair{vm::CallKind::Create, Address{}};
    }();

    vm::Message msg{
        .kind = to_address.first,
        .flags = 0,
        .depth = 0,
        .gas = static_cast<int64_t>(tx_.gas_limit - intrinsic_gas<traits>(tx_)),
        .recipient = to_address.second,
        .sender = sender_,
        .input_data = tx_.data.data(),
        .input_size = tx_.data.size(),
        .value = store_be_as<bytes32_t>(tx_.value),
        .create2_salt = {},
        .code_address = to_address.second,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = msg_memory_capacity,
    };
    return msg;
}

template <Traits traits>
vm::Result ExecuteTransactionNoValidation<traits>::operator()(
    State &state, StateHost<traits> &host)
{
    if constexpr (::monad::is_monad_trait_v<traits>) {
        init_reserve_balance_context<traits>(
            state,
            sender_,
            tx_,
            header_.base_fee_per_gas,
            host.i_,
            host.state_tracer_,
            host.chain_ctx_);
    }

    irrevocable_change<traits>(
        state,
        tx_,
        sender_,
        header_.base_fee_per_gas.value_or(0),
        header_.excess_blob_gas.value_or(0),
        chain_.get_blob_schedule(header_.timestamp));

    uint64_t auth_refund = 0u;
    if constexpr (traits::eip_7702_active()) {
        auth_refund = process_authorizations(state, host);
    }

    if constexpr (traits::eip_3651_active()) {
        host.access_account(header_.beneficiary);
    }

    state.access_account(sender_);
    for (auto const &ae : tx_.access_list) {
        state.access_account(ae.a);
        for (auto const &keys : ae.keys) {
            state.access_storage<traits>(ae.a, keys);
        }
    }
    if (MONAD_LIKELY(tx_.to)) {
        state.access_account(*tx_.to);
    }

    auto msg_memory = state.vm().message_memory_ref();
    auto msg = to_message(msg_memory, state.vm().message_memory_capacity());

    if constexpr (traits::eip_7702_active()) {
        if (tx_.to.has_value()) {
            if (auto const delegate = host.resolve_delegation(*tx_.to)) {
                msg.code_address = *delegate;
                msg.flags |= std::to_underlying(vm::CallFlags::Delegated);
                state.access_account(*delegate);
            }
        }
    }

    auto result =
        (msg.kind == vm::CallKind::Create || msg.kind == vm::CallKind::Create2)
            ? ::monad::execute_create_message<traits>(&host, state, msg)
            : ::monad::execute_call_message<traits>(&host, state, msg);

    result.gas_refund += auth_refund;
    return result;
}

EXPLICIT_TRAITS_CLASS(ExecuteTransactionNoValidation);

MONAD_NAMESPACE_END
