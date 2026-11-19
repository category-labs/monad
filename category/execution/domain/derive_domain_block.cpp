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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>
#include <limits>
#include <optional>
#include <utility>
#include <variant>

MONAD_DOMAIN_NAMESPACE_BEGIN

namespace
{
    struct SequencedTransaction
    {
        Transaction tx;
        Address sender;
    };

    std::optional<SequencedTransaction> derive_sequenced_transaction(
        DomainConfig const &domain, SequencedDomainPayload const &payload,
        DomainTransactionOpener const &open)
    {
        auto const plaintext = open(payload.payload);
        if (plaintext.has_error()) {
            LOG_WARNING(
                "Dropped a transaction of private domain {}: does not open",
                domain.chain_id);
            return std::nullopt;
        }
        byte_string_view encoded{plaintext.value()};
        auto decoded = rlp::decode_transaction(encoded);
        if (decoded.has_error() || !encoded.empty()) {
            LOG_WARNING(
                "Dropped a transaction of private domain {}: does not decode",
                domain.chain_id);
            return std::nullopt;
        }
        Transaction &tx = decoded.value();
        if (tx.sc.chain_id != uint256_t{domain.chain_id}) {
            LOG_WARNING(
                "Dropped a transaction of private domain {}: has another chain "
                "id",
                domain.chain_id);
            return std::nullopt;
        }
        auto const sender = recover_sender(tx);
        if (!sender.has_value()) {
            LOG_WARNING(
                "Dropped a transaction of private domain {}: sender does not "
                "recover",
                domain.chain_id);
            return std::nullopt;
        }
        if (*sender == DOMAIN_SYSTEM_RELAYER) {
            LOG_WARNING(
                "Dropped a transaction of private domain {}: is from the "
                "system relayer",
                domain.chain_id);
            return std::nullopt;
        }
        for (auto const &authorization : tx.authorization_list) {
            if (recover_authority(authorization) == DOMAIN_SYSTEM_RELAYER) {
                LOG_WARNING(
                    "Dropped a transaction of private domain {}: has a system "
                    "relayer authorization",
                    domain.chain_id);
                return std::nullopt;
            }
        }
        if (tx.gas_limit > purchased_domain_gas(payload.fee)) {
            LOG_WARNING(
                "Dropped a transaction of private domain {}: gas limit exceeds "
                "the gas its fee bought",
                domain.chain_id);
            return std::nullopt;
        }
        return SequencedTransaction{.tx = std::move(tx), .sender = *sender};
    }

    std::optional<Transaction> derive_message_delivery(
        DomainConfig const &domain, L1DomainMessage const &message)
    {
        if (message.nonce > std::numeric_limits<uint64_t>::max()) {
            LOG_WARNING(
                "Dropped a message of private domain {}: nonce exceeds 64 bits",
                domain.chain_id);
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
    // Sequenced transactions first, then deliveries.
    for (auto const &input : inputs.inputs) {
        auto const *const payload = std::get_if<SequencedDomainPayload>(&input);
        if (payload == nullptr) {
            continue;
        }
        auto sequenced = derive_sequenced_transaction(domain, *payload, open);
        if (sequenced.has_value()) {
            derived.transactions.push_back(std::move(sequenced->tx));
            derived.senders.push_back(sequenced->sender);
        }
    }
    for (auto const &input : inputs.inputs) {
        if (auto const *const message = std::get_if<L1DomainMessage>(&input)) {
            auto delivery = derive_message_delivery(domain, *message);
            if (delivery.has_value()) {
                derived.transactions.push_back(std::move(*delivery));
                derived.senders.push_back(DOMAIN_SYSTEM_RELAYER);
            }
        }
        else if (std::holds_alternative<EncryptedL1DomainMessage>(input)) {
            LOG_WARNING(
                "Dropped an encrypted message of private domain {}, which this "
                "version does not deliver",
                domain.chain_id);
        }
    }
    return std::optional{std::move(derived)};
}

MONAD_DOMAIN_NAMESPACE_END
