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

#include <category/core/assert.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>

#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <cstdint>
#include <memory>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint32_t RELAY_L1_MESSAGE_SELECTOR = monad::abi_encode_selector(
    "relayL1Message(uint64,address,address,bytes,uint256)");
static_assert(RELAY_L1_MESSAGE_SELECTOR == 0x70c0a876);

// Private key of SYSTEM_SENDER. Hardcoding it is intentional: it is public by
// design, and monad-bft hardcodes the same key to sign L1 system transactions.
constexpr uint8_t SYSTEM_SENDER_KEY[32] = {
    0xb0, 0x35, 0x8e, 0x6d, 0x70, 0x1a, 0x95, 0x5d, 0x99, 0x26, 0x67,
    0x6f, 0x22, 0x7e, 0x40, 0x17, 0x27, 0x63, 0x29, 0x6b, 0x31, 0x7f,
    0xf5, 0x54, 0xe4, 0x9c, 0xdf, 0x2c, 0x2c, 0x35, 0xf8, 0xa7};

monad::Secp256k1Signature sign_as_system_sender(monad::Transaction const &tx)
{
    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        context(
            secp256k1_context_create(SECP256K1_CONTEXT_SIGN),
            &secp256k1_context_destroy);
    auto const hash =
        monad::keccak256(monad::rlp::encode_transaction_for_signing(tx));
    secp256k1_ecdsa_recoverable_signature signature;
    MONAD_ASSERT(
        secp256k1_ecdsa_sign_recoverable(
            context.get(),
            &signature,
            hash.bytes,
            SYSTEM_SENDER_KEY,
            secp256k1_nonce_function_rfc6979,
            nullptr) == 1);
    uint8_t compact[64];
    int recovery_id = 0;
    secp256k1_ecdsa_recoverable_signature_serialize_compact(
        context.get(), compact, &recovery_id, &signature);
    return monad::Secp256k1Signature{
        .r = monad::load_be_unsafe<monad::uint256_t>(compact),
        .s = monad::load_be_unsafe<monad::uint256_t>(compact + 32),
        .y_parity = static_cast<uint8_t>(recovery_id)};
}

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
    Transaction tx{
        .sc = {.chain_id = uint256_t{domain_chain_id}},
        .nonce = message_nonce,
        .max_fee_per_gas = base_fee_per_gas,
        .gas_limit = gas_limit,
        .value = 0,
        .to = spoke,
        .type = TransactionType::legacy,
        .data = encode_relay_l1_message(
            source_chain_id, from, to, data, message_nonce)};
    tx.sc.signature = sign_as_system_sender(tx);
    return tx;
}

MONAD_NAMESPACE_END
