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
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

// One DomainHub.DomainTransactionSequenced event: a successful
// sequenceToDomain call, made directly or through another contract.
struct SequencedDomainPayload
{
    uint64_t domain_chain_id{};
    // Index of the L1 transaction whose receipt holds the event.
    size_t l1_transaction_index{};
    // The `rlpTx` argument: the HPKE envelope of one domain transaction.
    byte_string payload{};
    // Wei paid for the transaction on L1.
    uint256_t fee{};

    friend bool operator==(
        SequencedDomainPayload const &,
        SequencedDomainPayload const &) = default;
};

// One DomainHub.L1MessageRecorded event. `source_chain_id`/`from` are the
// hub-authenticated origin: the L1 chain and its caller for an ordinary send,
// or the source domain and sender of a domain message the hub relayed.
struct L1DomainMessage
{
    uint64_t domain_chain_id{};
    uint64_t source_chain_id{};
    Address from{};
    Address to{};
    byte_string data{};
    uint256_t nonce{};
    // Wei paid for the delivery on L1.
    uint256_t fee{};
    size_t l1_transaction_index{};

    friend bool
    operator==(L1DomainMessage const &, L1DomainMessage const &) = default;
};

// The hub events of the given domains in one L1 block. Each list is in
// receipt and log order; for messages that is hub nonce order.
struct DomainHubEvents
{
    std::vector<uint64_t> registered_domains;
    std::vector<SequencedDomainPayload> sequenced;
    std::vector<L1DomainMessage> messages;

    friend bool
    operator==(DomainHubEvents const &, DomainHubEvents const &) = default;
};

// Scans L1 receipts for DomainHub.DomainRegistered,
// DomainTransactionSequenced and L1MessageRecorded. Receipt blooms reject
// unrelated receipts
// before their logs are visited. Only events of `domain_ids` are decoded, so
// a malformed event for another domain never affects this node; a malformed
// event for one of them is an error. `domain_ids` must be sorted and
// deduplicated.
Result<DomainHubEvents> scan_domain_hub_events(
    std::span<Receipt const>, Address const &domain_hub,
    std::span<uint64_t const> domain_ids);

MONAD_NAMESPACE_END
