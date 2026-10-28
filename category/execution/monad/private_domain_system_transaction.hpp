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
// relayL1Message from this address only. The client pins it as the sender of
// the transactions it derives and refuses it as the recovered sender of any
// sequenced transaction.
inline constexpr Address DOMAIN_SYSTEM_RELAYER =
    address_from_hex("0xffffFFFfFFffffffffffffffFfFFFfffFFFfFFfE");

// ABI calldata of DomainSpoke.relayL1Message.
byte_string encode_relay_l1_message(
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint256_t const &message_nonce);

// Unsigned legacy transaction delivering one message to the spoke; its sender
// is DOMAIN_SYSTEM_RELAYER by protocol. `max_fee_per_gas` is the L1 base fee,
// the floor shared validation enforces; nothing is charged. `gas_limit` is
// purchased_domain_gas of the message's fee.
Transaction make_domain_system_transaction(
    uint64_t domain_chain_id, Address const &spoke, uint64_t relayer_nonce,
    uint256_t const &base_fee_per_gas, uint64_t gas_limit,
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint256_t const &message_nonce);

MONAD_NAMESPACE_END
