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
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Reserved sender of the system transactions that deliver L1 -> domain
// messages. Mirrors DomainSpoke.SYSTEM_RELAYER, which admits
// relayL1Message from this address only. No private key is known for it:
// derivation pins it as the sender of the transactions it builds, and drops
// any sequenced transaction whose recovered sender is this address.
inline constexpr Address DOMAIN_SYSTEM_RELAYER =
    address_from_hex("0xffffFFFfFFffffffffffffffFfFFFfffFFFfFFfE");

// ABI calldata of
// DomainSpoke.relayL1Message(uint64 sourceChainId, address from, address to,
// bytes data, uint256 nonce), where `sourceChainId`/`from` are the origin the
// hub authenticated (the L1 chain and its caller, or the source domain and
// sender of a natively forwarded domain message) and `nonce` is the hub's
// per-domain delivery nonce.
byte_string encode_relay_l1_message(
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint256_t const &message_nonce);

// Builds the legacy transaction that delivers one L1 -> domain message to the
// domain spoke. The transaction is not signed: its sender is fixed by protocol
// and supplied alongside it, never recovered. The signature fields hold a
// constant placeholder so the transaction round-trips through the standard
// RLP encoding, hashing and storage like any other domain transaction.
//
// Its nonce is the hub's message nonce, so building it needs no domain state.
// It is not an account nonce: the spoke's strictly increasing message nonce
// provides ordering and replay protection.
// Its gas price is the domain block's base fee, which nothing is ever charged
// for, and its gas limit is the gas the message's fee bought on L1.
Transaction make_domain_system_transaction(
    uint64_t domain_chain_id, Address const &spoke,
    uint256_t const &base_fee_per_gas, uint64_t gas_limit,
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint64_t message_nonce);

MONAD_NAMESPACE_END
