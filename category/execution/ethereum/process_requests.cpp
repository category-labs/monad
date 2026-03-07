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

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <intx/intx.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <Traits traits>
void system_call(
    Chain const &chain, State &state, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer, BlockHeader const &header,
    Address const &contract_address, ChainContext<traits> const &chain_ctx)
{
    // as per eip-7002, eip-7251
    constexpr auto SYSTEM_ADDRESS =
        0xfffffffffffffffffffffffffffffffffffffffe_address;
    if (!state.account_exists(contract_address)) {
        return;
    }

    evmc_tx_context tx_context = {
        .tx_gas_price = {},
        .tx_origin = SYSTEM_ADDRESS,
        .block_coinbase = header.beneficiary,
        .block_number = static_cast<int64_t>(header.number),
        .block_timestamp = static_cast<int64_t>(header.timestamp),
        .block_gas_limit = static_cast<int64_t>(header.gas_limit),
        .block_prev_randao = header.difficulty
                                 ? to_bytes(to_big_endian(header.difficulty))
                                 : header.prev_randao,
        .chain_id = to_bytes(to_big_endian(chain.get_chain_id())),
        .block_base_fee =
            to_bytes(to_big_endian(header.base_fee_per_gas.value_or(0))),
        .blob_base_fee = to_bytes(to_big_endian(
            get_base_fee_per_blob_gas(header.excess_blob_gas.value_or(0)))),
        .blob_hashes = nullptr,
        .blob_hashes_count = 0,
        .initcodes = nullptr,
        .initcodes_count = 0,
    };

    evmc_message msg = {
        .kind = EVMC_CALL,
        .flags = 0,
        .depth = 0,
        .gas = 30'000'000, // as per eip-7002, eip-7251
        .recipient = contract_address,
        .sender = SYSTEM_ADDRESS,
        .input_data = nullptr,
        .input_size = 0,
        .value = {},
        .create2_salt = {},
        .code_address = contract_address,
        .memory_handle = nullptr,
        .memory = nullptr,
        .memory_capacity = 0,
    };

    state.access_account(contract_address);

    NoopCallTracer call_tracer;
    Transaction const empty_tx{};
    EvmcHost<traits> host{
        call_tracer,
        tx_context,
        block_hash_buffer,
        state,
        empty_tx,
        header.base_fee_per_gas,
        0,
        chain_ctx};

    auto const hash = state.get_code_hash(contract_address);
    auto const code = state.read_code(hash);

    // as per EIP-7002/EIP-7251,
    //   system call failures are non-fatal and must not revert the block
    [[maybe_unused]] auto result =
        block_state.vm().template execute<traits>(host, &msg, hash, code);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
void process_requests(
    Chain const &chain, State &state, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer, BlockHeader const &header,
    ChainContext<traits> const &chain_ctx)
{
    // EIP-7002
    // Code is set in the hive genesis.
    constexpr auto WITHDRAWAL_REQUEST_ADDRESS =
        0x00000961ef480eb55e80d19ad83579a64c007002_address;
    system_call<traits>(
        chain,
        state,
        block_state,
        block_hash_buffer,
        header,
        WITHDRAWAL_REQUEST_ADDRESS,
        chain_ctx);

    // EIP-7251
    // Code is set in the hive genesis.
    constexpr auto CONSOLIDATION_REQUEST_ADDRESS =
        0x0000bbddc7ce488642fb579f8b00f3a590007251_address;
    system_call<traits>(
        chain,
        state,
        block_state,
        block_hash_buffer,
        header,
        CONSOLIDATION_REQUEST_ADDRESS,
        chain_ctx);
}

EXPLICIT_TRAITS(process_requests);

MONAD_NAMESPACE_END

