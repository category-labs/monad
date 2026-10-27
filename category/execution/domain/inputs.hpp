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
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/domain/config.hpp>

#include <cstdint>
#include <optional>
#include <variant>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

// One DomainHub.DomainTransactionSequenced event: a successful
// sequenceToDomain call, made directly or through another contract.
struct SequencedDomainPayload
{
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
    uint64_t source_chain_id{};
    Address from{};
    Address to{};
    byte_string data{};
    uint256_t nonce{};
    // Wei paid for the delivery on L1.
    uint256_t fee{};

    friend bool
    operator==(L1DomainMessage const &, L1DomainMessage const &) = default;
};

// One DomainHub.EncryptedL1MessageRecorded event. It is not delivered, but
// still gives the domain a block.
struct EncryptedL1DomainMessage
{
    friend bool operator==(
        EncryptedL1DomainMessage const &,
        EncryptedL1DomainMessage const &) = default;
};

using DomainInput = std::variant<
    SequencedDomainPayload, L1DomainMessage, EncryptedL1DomainMessage>;

// Everything one L1 block holds for one domain: what derivation reads, and
// all it reads.
struct DomainInputs
{
    // Of the L1 block. slot_number (EIP-7843) is present iff its header has
    // it.
    uint64_t l1_block_number{};
    uint64_t timestamp{};
    bytes32_t prev_randao{};
    std::optional<uint64_t> slot_number{};

    // Whether the L1 block registers the domain.
    bool registered{};
    // What the hub accepted for the domain in the L1 block, in the order it
    // accepted it; for messages that is hub nonce order.
    std::vector<DomainInput> inputs{};

    friend bool
    operator==(DomainInputs const &, DomainInputs const &) = default;
};

MONAD_DOMAIN_NAMESPACE_END
