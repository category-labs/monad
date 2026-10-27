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

#include <category/execution/monad/private_domain_system_transaction.hpp>

#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>

#include <cstdint>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint32_t RELAY_L1_MESSAGE_SELECTOR = monad::abi_encode_selector(
    "relayL1Message(uint64,address,address,bytes,uint256)");
static_assert(RELAY_L1_MESSAGE_SELECTOR == 0x70c0a876);

// Any nonzero canonical value satisfies the shared signature well-formedness
// check (EIP-2); the sender is never recovered from it.
constexpr monad::Secp256k1Signature PLACEHOLDER_SIGNATURE{
    .r = 1, .s = 1, .y_parity = 0};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

byte_string encode_relay_l1_message(
    uint64_t const source_chain_id, Address const &from, Address const &to,
    byte_string_view const data, uint256_t const &message_nonce)
{
    byte_string calldata{
        static_cast<uint8_t>(RELAY_L1_MESSAGE_SELECTOR >> 24),
        static_cast<uint8_t>(RELAY_L1_MESSAGE_SELECTOR >> 16),
        static_cast<uint8_t>(RELAY_L1_MESSAGE_SELECTOR >> 8),
        static_cast<uint8_t>(RELAY_L1_MESSAGE_SELECTOR)};
    AbiEncoder encoder;
    encoder.add_uint(u64_be{source_chain_id});
    encoder.add_address(from);
    encoder.add_address(to);
    encoder.add_bytes(data);
    encoder.add_uint(u256_be{message_nonce});
    calldata += encoder.encode_final();
    return calldata;
}

Transaction make_domain_system_transaction(
    uint64_t const domain_chain_id, Address const &spoke,
    uint256_t const &base_fee_per_gas, uint64_t const gas_limit,
    uint64_t const source_chain_id, Address const &from, Address const &to,
    byte_string_view const data, uint64_t const message_nonce)
{
    return Transaction{
        .sc =
            {.signature = PLACEHOLDER_SIGNATURE,
             .chain_id = uint256_t{domain_chain_id}},
        .nonce = message_nonce,
        .max_fee_per_gas = base_fee_per_gas,
        .gas_limit = gas_limit,
        .value = 0,
        .to = spoke,
        .type = TransactionType::legacy,
        .data = encode_relay_l1_message(
            source_chain_id, from, to, data, message_nonce)};
}

MONAD_NAMESPACE_END
