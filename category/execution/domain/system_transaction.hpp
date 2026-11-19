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
#include <category/core/int.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/monad/system_sender.hpp>

#include <cstdint>

MONAD_DOMAIN_NAMESPACE_BEGIN

// Sender of the system transactions that deliver L1 messages to the domain
// spoke. Mirrors DomainSpoke.SYSTEM_RELAYER.
inline constexpr Address DOMAIN_SYSTEM_RELAYER = SYSTEM_SENDER;

// Calldata of DomainSpoke.relayL1Message(uint64 sourceChainId, address from,
// address to, bytes data, uint256 nonce). `message_nonce` is the hub's
// per-domain message nonce.
byte_string encode_relay_l1_message(
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint64_t message_nonce);

// Builds the transaction that delivers one L1 message to the domain spoke,
// signed by DOMAIN_SYSTEM_RELAYER. The transaction nonce is the hub's
// message nonce, not an account nonce.
Transaction make_domain_system_transaction(
    uint64_t domain_chain_id, Address const &spoke,
    uint256_t const &base_fee_per_gas, uint64_t gas_limit,
    uint64_t source_chain_id, Address const &from, Address const &to,
    byte_string_view data, uint64_t message_nonce);

MONAD_DOMAIN_NAMESPACE_END
