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

#include <category/execution/monad/private_domain_derivation.hpp>

#include <category/core/assert.h>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/ordered_trie.hpp>
#include <category/execution/monad/private_domain_scanner.hpp>
#include <category/execution/monad/private_domain_system_transaction.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    // Counts the items of one domain block that derivation drops, to log
    // them once per block instead of once per item.
    struct Dropped
    {
        size_t count{};
        std::string_view first_reason{};

        void add(std::string_view const reason)
        {
            if (count++ == 0) {
                first_reason = reason;
            }
        }
    };

    struct SequencedTransaction
    {
        Transaction tx;
        Address sender;
    };

    std::optional<SequencedTransaction> derive_sequenced_transaction(
        SequencedDomainPayload const &payload,
        DomainTransactionOpener const &open, Dropped &dropped)
    {
        auto const plaintext = open(payload.domain_chain_id, payload.payload);
        if (plaintext.has_error()) {
            dropped.add("transaction does not open");
            return std::nullopt;
        }
        byte_string_view encoded{plaintext.value()};
        auto decoded = rlp::decode_transaction(encoded);
        if (decoded.has_error() || !encoded.empty()) {
            dropped.add("transaction does not decode");
            return std::nullopt;
        }
        Transaction &tx = decoded.value();
        if (tx.sc.chain_id != uint256_t{payload.domain_chain_id}) {
            dropped.add("transaction has another chain id");
            return std::nullopt;
        }
        auto const sender = recover_sender(tx);
        if (!sender.has_value()) {
            dropped.add("transaction sender does not recover");
            return std::nullopt;
        }
        if (*sender == DOMAIN_SYSTEM_RELAYER) {
            dropped.add("transaction is from the system relayer");
            return std::nullopt;
        }
        if (tx.gas_limit > purchased_domain_gas(payload.fee)) {
            dropped.add("transaction gas limit exceeds the gas its fee bought");
            return std::nullopt;
        }
        return SequencedTransaction{.tx = std::move(tx), .sender = *sender};
    }

    std::optional<Transaction> derive_message_delivery(
        DomainDerivationState const &domain, L1DomainMessage const &message,
        Dropped &dropped)
    {
        if (message.nonce > std::numeric_limits<uint64_t>::max()) {
            dropped.add("message nonce exceeds 64 bits");
            return std::nullopt;
        }
        return make_domain_system_transaction(
            domain.domain_chain_id,
            domain.spoke,
            DOMAIN_GAS_PRICE,
            purchased_domain_gas(message.fee),
            message.source_chain_id,
            message.from,
            message.to,
            message.data,
            static_cast<uint64_t>(message.nonce));
    }

    ProposedDomainHeader make_header(
        DomainDerivationInput const &input, uint64_t const domain_chain_id,
        uint64_t const number, std::span<Transaction const> const txs)
    {
        std::vector<byte_string> encoded;
        encoded.reserve(txs.size());
        for (auto const &tx : txs) {
            encoded.push_back(rlp::encode_transaction(tx));
        }
        return ProposedDomainHeader{
            .domain_chain_id = domain_chain_id,
            .number = number,
            .l1_block_number = input.l1_header.number,
            .l1_block_id = input.l1_block_id,
            .timestamp = input.l1_header.timestamp,
            .mix_hash = input.l1_header.prev_randao,
            .gas_limit = DOMAIN_BLOCK_GAS_LIMIT,
            .base_fee_per_gas = DOMAIN_GAS_PRICE,
            .transactions_root = ordered_trie_root(encoded)};
    }
}

uint64_t purchased_domain_gas(uint256_t const &fee)
{
    uint256_t const gas = fee / DOMAIN_GAS_PRICE;
    return gas < DOMAIN_BLOCK_GAS_LIMIT ? static_cast<uint64_t>(gas)
                                        : DOMAIN_BLOCK_GAS_LIMIT;
}

Result<std::vector<DerivedDomainBlock>> derive_domain_blocks(
    DomainDerivationInput const &input,
    std::span<DomainDerivationState const> const domains,
    DomainTransactionOpener const &open)
{
    std::vector<uint64_t> domain_ids;
    domain_ids.reserve(domains.size());
    for (auto const &domain : domains) {
        domain_ids.push_back(domain.domain_chain_id);
    }
    MONAD_ASSERT(
        std::ranges::adjacent_find(domain_ids) == domain_ids.end() &&
        std::ranges::is_sorted(domain_ids));

    BOOST_OUTCOME_TRY(
        auto const events,
        scan_domain_hub_events(
            input.l1_receipts, input.domain_hub, domain_ids));

    std::vector<DerivedDomainBlock> blocks;
    for (auto const &domain : domains) {
        uint64_t const id = domain.domain_chain_id;
        auto const of_domain = [id](auto const &event) {
            return event.domain_chain_id == id;
        };
        auto const event_count =
            std::ranges::count_if(events.sequenced, of_domain) +
            std::ranges::count_if(events.messages, of_domain);

        uint64_t number;
        if (std::ranges::contains(events.registered_domains, id)) {
            if (domain.latest_header.has_value()) {
                // The hub registers a domain at most once, so this node's
                // genesis came from somewhere else.
                LOG_ERROR(
                    "Ignoring L1 block {} of private domain {}: it registers "
                    "the domain, which already has block {}",
                    input.l1_header.number,
                    id,
                    domain.latest_header->number);
                continue;
            }
            number = 0;
        }
        else if (event_count == 0) {
            continue;
        }
        else if (!domain.latest_header.has_value()) {
            LOG_ERROR(
                "Dropped {} hub event(s) of private domain {} in L1 block {}: "
                "this node has not derived its registration",
                event_count,
                id,
                input.l1_header.number);
            continue;
        }
        else {
            number = domain.latest_header->number + 1;
        }

        DerivedDomainBlock derived;
        Dropped dropped;
        for (auto const &payload : events.sequenced) {
            if (payload.domain_chain_id != id) {
                continue;
            }
            auto sequenced =
                derive_sequenced_transaction(payload, open, dropped);
            if (sequenced.has_value()) {
                derived.block.transactions.push_back(std::move(sequenced->tx));
                derived.senders.push_back(sequenced->sender);
            }
        }
        for (auto const &message : events.messages) {
            if (message.domain_chain_id != id) {
                continue;
            }
            auto delivery = derive_message_delivery(domain, message, dropped);
            if (delivery.has_value()) {
                derived.block.transactions.push_back(std::move(*delivery));
                derived.senders.push_back(DOMAIN_SYSTEM_RELAYER);
            }
        }

        if (dropped.count != 0) {
            LOG_WARNING(
                "Dropped {} item(s) of private domain {} in L1 block {}; "
                "first: {}",
                dropped.count,
                id,
                input.l1_header.number,
                dropped.first_reason);
        }
        derived.block.header =
            make_header(input, id, number, derived.block.transactions);
        blocks.push_back(std::move(derived));
    }
    return blocks;
}

MONAD_NAMESPACE_END
