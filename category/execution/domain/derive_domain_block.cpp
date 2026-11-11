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

#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <string_view>
#include <utility>
#include <variant>

MONAD_DOMAIN_NAMESPACE_BEGIN

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
        DomainConfig const &domain, SequencedDomainPayload const &payload,
        DomainTransactionOpener const &open, Dropped &dropped)
    {
        auto const plaintext = open(payload.payload);
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
        if (tx.sc.chain_id != uint256_t{domain.chain_id}) {
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
        for (auto const &authorization : tx.authorization_list) {
            if (recover_authority(authorization) == DOMAIN_SYSTEM_RELAYER) {
                dropped.add("transaction has a system relayer authorization");
                return std::nullopt;
            }
        }
        if (tx.gas_limit > purchased_domain_gas(payload.fee)) {
            dropped.add("transaction gas limit exceeds the gas its fee bought");
            return std::nullopt;
        }
        return SequencedTransaction{.tx = std::move(tx), .sender = *sender};
    }

    std::optional<Transaction> derive_message_delivery(
        DomainConfig const &domain, L1DomainMessage const &message,
        Dropped &dropped)
    {
        if (message.nonce > std::numeric_limits<uint64_t>::max()) {
            dropped.add("message nonce exceeds 64 bits");
            return std::nullopt;
        }
        return make_domain_system_transaction(
            domain.chain_id,
            domain.spoke,
            DOMAIN_GAS_PRICE,
            purchased_domain_gas(message.fee),
            message.source_chain_id,
            message.from,
            message.to,
            message.data,
            static_cast<uint64_t>(message.nonce));
    }
}

uint64_t purchased_domain_gas(uint256_t const &fee)
{
    uint256_t const gas = fee / DOMAIN_GAS_PRICE;
    return gas < DOMAIN_BLOCK_GAS_LIMIT ? static_cast<uint64_t>(gas)
                                        : DOMAIN_BLOCK_GAS_LIMIT;
}

Result<std::optional<DerivedDomainBlock>> derive_domain_block(
    DomainInputs const &inputs, DomainConfig const &domain,
    uint64_t const next_domain_block, DomainTransactionOpener const &open)
{
    // The domain has its genesis, block 0, iff the next block is past it.
    bool const has_genesis = next_domain_block != 0;
    if (inputs.registered) {
        if (MONAD_UNLIKELY(has_genesis)) {
            return DomainDerivationError::AlreadyRegistered;
        }
    }
    else if (inputs.inputs.empty()) {
        return std::optional<DerivedDomainBlock>{};
    }
    else if (MONAD_UNLIKELY(!has_genesis)) {
        return DomainDerivationError::NotRegistered;
    }

    DerivedDomainBlock derived{
        .number = next_domain_block,
        .l1_block_number = inputs.l1_block_number,
        .timestamp = inputs.timestamp,
        .prev_randao = inputs.prev_randao,
        .slot_number = inputs.slot_number};
    Dropped dropped;
    // Sequenced transactions first, then deliveries.
    for (auto const &input : inputs.inputs) {
        auto const *const payload = std::get_if<SequencedDomainPayload>(&input);
        if (payload == nullptr) {
            continue;
        }
        auto sequenced =
            derive_sequenced_transaction(domain, *payload, open, dropped);
        if (sequenced.has_value()) {
            derived.transactions.push_back(std::move(sequenced->tx));
            derived.senders.push_back(sequenced->sender);
        }
    }
    for (auto const &input : inputs.inputs) {
        if (auto const *const message = std::get_if<L1DomainMessage>(&input)) {
            auto delivery = derive_message_delivery(domain, *message, dropped);
            if (delivery.has_value()) {
                derived.transactions.push_back(std::move(*delivery));
                derived.senders.push_back(DOMAIN_SYSTEM_RELAYER);
            }
        }
        else if (std::holds_alternative<EncryptedL1DomainMessage>(input)) {
            dropped.add("encrypted L1 message, which this version does not "
                        "deliver");
        }
    }
    if (dropped.count != 0) {
        LOG_WARNING(
            "Dropped {} item(s) of private domain {} in L1 block {}; "
            "first: {}",
            dropped.count,
            domain.chain_id,
            inputs.l1_block_number,
            dropped.first_reason);
    }
    return std::optional{std::move(derived)};
}

MONAD_DOMAIN_NAMESPACE_END
