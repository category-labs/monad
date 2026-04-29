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

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <silkpre/sha256.h>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>
#include <intx/intx.hpp>

using BOOST_OUTCOME_V2_NAMESPACE::success;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <Traits traits>
Result<byte_string> system_call(
    Chain const &chain, State &state, BlockHashBuffer const &block_hash_buffer,
    BlockHeader const &header, Address const &contract_address,
    ChainContext<traits> const &chain_ctx)
{
    constexpr auto SYSTEM_ADDRESS =
        0xfffffffffffffffffffffffffffffffffffffffe_address;

    // Per EIP-7002/EIP-7251: if there is no code at the predeploy address,
    // the block MUST be marked invalid.
    auto const hash = state.get_code_hash(contract_address);
    if (MONAD_UNLIKELY(hash == NULL_HASH)) {
        return BlockError::SystemCallMissingCode;
    }
    auto const code = state.read_code(hash);

    evmc_tx_context const tx_context = {
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

    auto msg_memory = state.vm().message_memory_ref();
    evmc_message const msg = {
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
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = state.vm().message_memory_capacity(),
    };

    state.access_account(contract_address);

    NoopCallTracer noop_tracer;
    Transaction const empty_tx{};
    EvmcHost<traits> host{
        noop_tracer,
        tx_context,
        block_hash_buffer,
        state,
        empty_tx,
        header.base_fee_per_gas,
        0,
        chain_ctx};

    // We intentionally invoke the VM directly: system calls must not go
    // through the regular call path which does state push/pop -- a revert
    // from call()'s post_call would roll back the system contract's state
    // changes, whereas per EIP-7002/EIP-7251 a failed system call must
    // invalidate the entire block instead.
    auto const result =
        state.vm().template execute<traits>(host, &msg, hash, code);

    // "if the call fails or returns an error, the block MUST be invalidated"
    if (MONAD_UNLIKELY(result.status_code != EVMC_SUCCESS)) {
        return BlockError::SystemCallFailed;
    }

    return byte_string(
        result.output_data, result.output_data + result.output_size);
}

bytes32_t compute_requests_hash(
    byte_string const &withdrawal_output,
    byte_string const &consolidation_output)
{
    // at most 3 types * 32 bytes
    uint8_t inner_hashes_buf[96];
    size_t inner_hashes_len = 0;

    auto const hash_request = [&](uint8_t type, byte_string const &data) {
        // EIP-7685 flat requests encoding: empty request types are excluded
        // from the hash.
        if (data.empty()) {
            return;
        }
        byte_string buf;
        buf.reserve(1 + data.size());
        buf.push_back(type);
        buf.insert(buf.end(), data.begin(), data.end());
        silkpre_sha256(
            inner_hashes_buf + inner_hashes_len, buf.data(), buf.size(), true);
        inner_hashes_len += 32;
    };

    // TODO: EIP-6110 deposits
    hash_request(0x00, {});
    hash_request(0x01, withdrawal_output);
    hash_request(0x02, consolidation_output);

    bytes32_t outer_hash;
    silkpre_sha256(outer_hash.bytes, inner_hashes_buf, inner_hashes_len, true);
    return outer_hash;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<bytes32_t> process_requests(
    Chain const &chain, State &state, BlockHashBuffer const &block_hash_buffer,
    BlockHeader const &header, ChainContext<traits> const &chain_ctx)
{
    // EIP-7002
    constexpr auto WITHDRAWAL_REQUEST_ADDRESS =
        0x00000961ef480eb55e80d19ad83579a64c007002_address;
    BOOST_OUTCOME_TRY(
        auto const withdrawal_output,
        system_call<traits>(
            chain,
            state,
            block_hash_buffer,
            header,
            WITHDRAWAL_REQUEST_ADDRESS,
            chain_ctx));

    // EIP-7251
    constexpr auto CONSOLIDATION_REQUEST_ADDRESS =
        0x0000bbddc7ce488642fb579f8b00f3a590007251_address;
    BOOST_OUTCOME_TRY(
        auto const consolidation_output,
        system_call<traits>(
            chain,
            state,
            block_hash_buffer,
            header,
            CONSOLIDATION_REQUEST_ADDRESS,
            chain_ctx));

    return compute_requests_hash(withdrawal_output, consolidation_output);
}

EXPLICIT_EVM_TRAITS(process_requests);

MONAD_NAMESPACE_END
