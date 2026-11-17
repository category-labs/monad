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
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/inputs.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

class L1Source;

// What the hub's state holds of a domain as of one L1 block: its latest
// attested checkpoint, and in its input queue the inputs of every block that
// checkpoint does not cover. With the domain's state at the checkpoint, that
// is all it takes to derive the domain up to that L1 block.
struct PendingDomainInputs
{
    // The attested hash of the domain's last block the checkpoint covers.
    // Zero until a checkpoint is attested.
    bytes32_t attested_block_hash{};
    // The number of the first block the checkpoint does not cover: 0 until a
    // checkpoint is attested.
    uint64_t next_block{};
    // The inputs of the blocks from `next_block` on, one element per block, up
    // to the domain's latest block. slot_number is always set, to zero if the
    // L1 block has none.
    std::vector<DomainInputs> blocks{};

    friend bool operator==(
        PendingDomainInputs const &, PendingDomainInputs const &) = default;
};

// The storage slot of the hub that holds `domain_chain_id`'s attested block
// hash.
bytes32_t attested_block_hash_slot(uint64_t domain_chain_id);

// The storage slot of word `index` of `domain_chain_id`'s input queue.
bytes32_t input_queue_slot(uint64_t domain_chain_id, uint64_t index);

// Reads `domain_chain_id`'s checkpoint and input queue from the storage of
// `hub` as of finalized L1 block `l1_block_number`. Empty if the domain is not
// registered by then. Fails like L1Source::read_storage, and with
// DomainDerivationError::MalformedInputQueue on a queue the hub cannot have
// written.
Result<std::optional<PendingDomainInputs>> read_pending_domain_inputs(
    L1Source const &, Address const &hub, uint64_t domain_chain_id,
    uint64_t l1_block_number);

MONAD_DOMAIN_NAMESPACE_END
