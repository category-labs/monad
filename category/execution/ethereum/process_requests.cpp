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

#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <silkpre_vendor/sha256.h>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>
#include <intx/intx.hpp>

#include <array>
#include <cstdint>
#include <utility>
#include <vector>

using BOOST_OUTCOME_V2_NAMESPACE::success;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint8_t DEPOSIT_REQUEST_TYPE = 0x00;
constexpr uint8_t WITHDRAWAL_REQUEST_TYPE = 0x01;
constexpr uint8_t CONSOLIDATION_REQUEST_TYPE = 0x02;

template <Traits traits>
Result<byte_string> system_call(
    Chain const &chain, State &state, BlockHashBuffer const &block_hash_buffer,
    BlockHeader const &header, Address const &contract_address,
    trace::StateTracer &state_tracer, ChainContext<traits> const &chain_ctx)
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
    trace::on_read_code(state_tracer, hash, code->intercode());

    evmc_tx_context const tx_context = {
        .tx_gas_price = {},
        .tx_origin = SYSTEM_ADDRESS,
        .block_coinbase = header.beneficiary,
        .block_number = static_cast<int64_t>(header.number),
        .block_timestamp = static_cast<int64_t>(header.timestamp),
        .block_gas_limit = static_cast<int64_t>(header.gas_limit),
        .block_prev_randao = header.difficulty
                                 ? store_be_as<bytes32_t>(header.difficulty)
                                 : header.prev_randao,
        .chain_id = store_be_as<bytes32_t>(chain.get_chain_id()),
        .block_base_fee =
            store_be_as<bytes32_t>(header.base_fee_per_gas.value_or(0)),
        .blob_base_fee =
            store_be_as<bytes32_t>(get_base_fee_per_blob_gas<traits>(
                header.excess_blob_gas.value_or(0))),
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
        state_tracer,
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

Result<void> consume_deposit_event_head(byte_string_view &cursor)
{
    auto const check_offset = [&](uint32_t expected) -> Result<void> {
        auto const actual = abi_decode_fixed<u256_be>(cursor);
        if (actual.has_error() || actual.value().native() != expected) {
            return BlockError::InvalidDepositLog;
        }
        return success();
    };

    BOOST_OUTCOME_TRY(check_offset(160));
    BOOST_OUTCOME_TRY(check_offset(256));
    BOOST_OUTCOME_TRY(check_offset(320));
    BOOST_OUTCOME_TRY(check_offset(384));
    BOOST_OUTCOME_TRY(check_offset(512));

    return success();
}

template <size_t N>
Result<void>
append_deposit_event_field(byte_string &deposits, byte_string_view &cursor)
{
    auto const field = abi_decode_dynamic_bytes_tail<N>(cursor);
    if (field.has_error()) {
        return BlockError::InvalidDepositLog;
    }
    deposits.append_range(field.value());
    return success();
}

Result<void>
append_deposit_request(byte_string &deposits, byte_string_view cursor)
{
    // EIP-6110 accepts one canonical 576-byte ABI log-data item emitted by the
    // deposit contract's DepositEvent(bytes,bytes,bytes,bytes,bytes). The
    // 5-word head occupies bytes [0, 160); each head word is an ABI offset from
    // the start of that event data to the corresponding dynamic `bytes` tail:
    //
    //   pubkey                  offset 160, size 48
    //   withdrawal_credentials  offset 256, size 32
    //   amount                  offset 320, size 8
    //   signature               offset 384, size 96
    //   index                   offset 512, size 8
    if (cursor.length() != 576) {
        return BlockError::InvalidDepositLog;
    }

    BOOST_OUTCOME_TRY(consume_deposit_event_head(cursor));

    BOOST_OUTCOME_TRY(append_deposit_event_field<48>(deposits, cursor));
    BOOST_OUTCOME_TRY(append_deposit_event_field<32>(deposits, cursor));
    BOOST_OUTCOME_TRY(append_deposit_event_field<8>(deposits, cursor));
    BOOST_OUTCOME_TRY(append_deposit_event_field<96>(deposits, cursor));
    BOOST_OUTCOME_TRY(append_deposit_event_field<8>(deposits, cursor));
    return success();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<byte_string>
extract_deposit_requests(std::span<Receipt const> const receipts)
{
    constexpr auto DEPOSIT_CONTRACT_ADDRESS =
        0x00000000219ab540356cbb839cbe05303d7705fa_address;
    constexpr auto DEPOSIT_EVENT_SIGNATURE_HASH =
        0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5_bytes32;
    byte_string deposits;
    for (auto const &receipt : receipts) {
        for (auto const &log : receipt.logs) {
            if (log.address != DEPOSIT_CONTRACT_ADDRESS || log.topics.empty() ||
                log.topics[0] != DEPOSIT_EVENT_SIGNATURE_HASH) {
                continue;
            }
            BOOST_OUTCOME_TRY(append_deposit_request(deposits, log.data));
        }
    }
    return deposits;
}

bytes32_t compute_requests_hash(std::span<BlockRequest const> const requests)
{
    std::vector<uint8_t> inner_hashes;
    inner_hashes.reserve(32 * requests.size());

    for (auto const &req : requests) {
        // EIP-7685 flat requests encoding: empty request data are excluded from
        // the hash.
        if (req.data.empty()) {
            continue;
        }

        bytes32_t inner;
        byte_string buf;
        buf.reserve(1 + req.data.size());
        buf.push_back(req.type);
        buf.append_range(req.data);
        monad_sha256(inner.bytes, buf.data(), buf.size(), true);
        inner_hashes.append_range(inner.bytes);
    }

    static constexpr uint8_t EMPTY_SHA256_INPUT = 0;
    bytes32_t outer_hash;
    uint8_t const *outer_input =
        inner_hashes.empty() ? &EMPTY_SHA256_INPUT : inner_hashes.data();
    monad_sha256(outer_hash.bytes, outer_input, inner_hashes.size(), true);
    return outer_hash;
}

template <Traits traits>
Result<bytes32_t> process_requests(
    Chain const &chain, State &state, BlockHashBuffer const &block_hash_buffer,
    BlockHeader const &header, trace::StateTracer &state_tracer,
    ChainContext<traits> const &chain_ctx,
    std::span<Receipt const> const receipts)
{
    BOOST_OUTCOME_TRY(auto deposit_output, extract_deposit_requests(receipts));

    // EIP-7002
    constexpr auto WITHDRAWAL_REQUEST_ADDRESS =
        0x00000961ef480eb55e80d19ad83579a64c007002_address;
    BOOST_OUTCOME_TRY(
        auto withdrawal_output,
        system_call<traits>(
            chain,
            state,
            block_hash_buffer,
            header,
            WITHDRAWAL_REQUEST_ADDRESS,
            state_tracer,
            chain_ctx));

    // EIP-7251
    constexpr auto CONSOLIDATION_REQUEST_ADDRESS =
        0x0000bbddc7ce488642fb579f8b00f3a590007251_address;
    BOOST_OUTCOME_TRY(
        auto consolidation_output,
        system_call<traits>(
            chain,
            state,
            block_hash_buffer,
            header,
            CONSOLIDATION_REQUEST_ADDRESS,
            state_tracer,
            chain_ctx));

    return compute_requests_hash(std::array<BlockRequest, 3>{{
        {DEPOSIT_REQUEST_TYPE, std::move(deposit_output)},
        {WITHDRAWAL_REQUEST_TYPE, std::move(withdrawal_output)},
        {CONSOLIDATION_REQUEST_TYPE, std::move(consolidation_output)},
    }});
}

EXPLICIT_EVM_TRAITS(process_requests);

MONAD_NAMESPACE_END
