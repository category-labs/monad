// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

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
// relayL1Message from this address only. No private key is known for it: the
// client pins it as the sender of the transactions it derives, and refuses it
// as the recovered sender of any sequenced transaction.
inline constexpr Address DOMAIN_SYSTEM_RELAYER =
    address_from_hex("0xffffFFFfFFffffffffffffffFfFFFfffFFFfFFfE");

// Fixed gas limit of every delivery transaction, so that the outcome of a
// delivery is identical on every node executing the same L1 block. It must
// exceed DomainSpoke.DELIVERY_GAS_STIPEND (2,000,000, the gas the spoke
// forwards to the target) by the relay's own overhead, so that a target which
// exhausts its stipend still leaves the spoke enough gas to record the failed
// delivery for retry instead of reverting the whole relay.
inline constexpr uint64_t DOMAIN_SYSTEM_TRANSACTION_GAS_LIMIT = 2'500'000;

// ABI calldata of
// DomainSpoke.relayL1Message(uint64 sourceChainId, address from, address to,
// bytes data, uint256 nonce), where `sourceChainId`/`from` are the origin the
// hub authenticated (the L1 chain and its caller, or the source domain and
// sender of a natively forwarded domain message) and `nonce` is the hub's
// per-domain delivery nonce.
byte_string encode_relay_l1_message(
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint256_t const &message_nonce);

// Builds the gasless legacy transaction that delivers one L1 -> domain
// message to the domain spoke. The transaction is not signed: its sender
// is fixed by protocol and supplied alongside it, never recovered. The
// signature fields hold a constant placeholder so the transaction passes the
// shared static validation and round-trips through the standard RLP
// encoding, hashing and storage like any other domain transaction. Its
// gas price is the L1 block's base fee, which the shared validation requires
// as a floor even for gasless execution; nothing is ever charged for it.
Transaction make_domain_system_transaction(
    uint64_t domain_chain_id, Address const &spoke, uint64_t relayer_nonce,
    uint256_t const &base_fee_per_gas, uint64_t source_chain_id,
    Address const &from, Address const &to, byte_string_view data,
    uint256_t const &message_nonce);

MONAD_NAMESPACE_END
