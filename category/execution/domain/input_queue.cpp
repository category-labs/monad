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

#include <category/execution/domain/input_queue.hpp>

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/deriver.hpp>
#include <category/execution/domain/hub_storage.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/l1_source.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_BEGIN

// The hub's storage layout. See InputQueue.sol and DomainHub.sol in
// category-labs/monad-domains.

// `mapping(uint64 domainChainId => bytes32 blockHash) blockHashes`.
constexpr uint8_t BLOCK_HASHES_SLOT = 3;

// Words of the queue's first page.
constexpr uint64_t LATEST_WORD = 0;
constexpr uint64_t STATE_WORD = 1;
// The data ring: word `i` is at `DATA_WORD + i % CAPACITY`.
constexpr uint64_t DATA_WORD = 128;
constexpr uint64_t CAPACITY = uint64_t{1} << 17;
constexpr uint8_t CHUNK_TAG = 1;

// Entry kinds.
constexpr uint8_t TRANSACTION = 1;
constexpr uint8_t MESSAGE = 2;
constexpr uint8_t ENCRYPTED_MESSAGE = 3;
constexpr uint8_t BLOCK = 4;

// Reads the queue's data ring word by word, as of one L1 block.
class QueueReader
{
    L1Source const &l1_;
    Address const &hub_;
    uint64_t domain_chain_id_;
    uint64_t l1_block_number_;

public:
    QueueReader(
        L1Source const &l1, Address const &hub, uint64_t const domain_chain_id,
        uint64_t const l1_block_number)
        : l1_{l1}
        , hub_{hub}
        , domain_chain_id_{domain_chain_id}
        , l1_block_number_{l1_block_number}
    {
    }

    Result<bytes32_t> read(bytes32_t const &slot) const
    {
        return l1_.read_storage(l1_block_number_, hub_, slot);
    }

    Result<bytes32_t> page_word(uint64_t const word) const
    {
        return read(input_queue_slot(domain_chain_id_, word));
    }

    Result<bytes32_t> data_word(uint64_t const position) const
    {
        return page_word(DATA_WORD + position % CAPACITY);
    }
};

// Decodes the payload of an input of `kind` that paid `fee`.
Result<DomainInput>
decode_input(uint8_t const kind, uint256_t const &fee, byte_string payload)
{
    switch (kind) {
    case TRANSACTION:
        return DomainInput{
            SequencedDomainPayload{.payload = std::move(payload), .fee = fee}};
    case MESSAGE: {
        if (payload.size() < sizeof(MessagePayloadHeader)) {
            return DomainDerivationError::MalformedInputQueue;
        }
        auto const header =
            unaligned_load<MessagePayloadHeader>(payload.data());
        return DomainInput{L1DomainMessage{
            .source_chain_id = header.source_chain_id.native(),
            .from = header.from,
            .to = header.to,
            .data = payload.substr(sizeof(MessagePayloadHeader)),
            .nonce = header.nonce.native(),
            .fee = fee}};
    }
    case ENCRYPTED_MESSAGE:
        return DomainInput{EncryptedL1DomainMessage{}};
    default:
        return DomainDerivationError::MalformedInputQueue;
    }
}

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

bytes32_t attested_block_hash_slot(uint64_t const domain_chain_id)
{
    // keccak256(abi.encode(uint64 domainChainId, uint256 BLOCK_HASHES_SLOT))
    uint8_t encoded[2 * 32]{};
    store_be(encoded + 24, domain_chain_id);
    encoded[2 * 32 - 1] = BLOCK_HASHES_SLOT;
    return to_bytes(keccak256({encoded, sizeof(encoded)}));
}

bytes32_t input_queue_slot(uint64_t const domain_chain_id, uint64_t const index)
{
    // The queue's first slot plus `index`, as a 256-bit big-endian sum.
    bytes32_t slot = latest_domain_block_slot(domain_chain_id);
    uint64_t carry = index;
    for (size_t i = sizeof(slot.bytes); i > 0 && carry != 0; --i) {
        carry += slot.bytes[i - 1];
        slot.bytes[i - 1] = static_cast<uint8_t>(carry);
        carry >>= 8;
    }
    return slot;
}

Result<std::optional<PendingDomainInputs>> read_pending_domain_inputs(
    L1Source const &l1, Address const &hub, uint64_t const domain_chain_id,
    uint64_t const l1_block_number)
{
    QueueReader const queue{l1, hub, domain_chain_id, l1_block_number};

    BOOST_OUTCOME_TRY(auto const latest, queue.page_word(LATEST_WORD));
    if (latest == bytes32_t{}) {
        return std::optional<PendingDomainInputs>{};
    }
    uint64_t const latest_block =
        load_hub_word<LatestBlockWord>(latest).domain_block_number.native();

    BOOST_OUTCOME_TRY(auto const state_word, queue.page_word(STATE_WORD));
    auto const state = load_hub_word<QueueStateWord>(state_word);
    uint64_t const tail = state.tail.native();
    uint64_t const head = state.head.native();
    if (head < tail || head - tail > CAPACITY) {
        return DomainDerivationError::MalformedInputQueue;
    }

    PendingDomainInputs pending;
    BOOST_OUTCOME_TRY(
        pending.attested_block_hash,
        queue.read(attested_block_hash_slot(domain_chain_id)));

    uint64_t position = tail;
    while (position < head) {
        BOOST_OUTCOME_TRY(auto const word, queue.data_word(position));
        // Every entry starts with its kind.
        if (word.bytes[0] == BLOCK) {
            // A block entry, then `prevrandao`.
            if (head - position < 2) {
                return DomainDerivationError::MalformedInputQueue;
            }
            auto const entry = load_hub_word<BlockEntryWord>(word);
            uint64_t const number = entry.domain_block_number.native();
            if (pending.blocks.empty()) {
                pending.next_block = number;
            }
            else if (number != pending.next_block + pending.blocks.size()) {
                return DomainDerivationError::MalformedInputQueue;
            }
            DomainInputs inputs;
            inputs.l1_block_number = entry.l1_block_number.native();
            inputs.timestamp = entry.l1_timestamp.native();
            BOOST_OUTCOME_TRY(
                inputs.prev_randao, queue.data_word(position + 1));
            inputs.slot_number =
                static_cast<uint64_t>(load_be_field(entry.slot_number));
            // The registering L1 block is the domain's block 0.
            inputs.registered = number == 0;
            pending.blocks.push_back(std::move(inputs));
            position += 2;
            continue;
        }

        // An input: its header, then its payload in chunks.
        if (pending.blocks.empty()) {
            // The first entry the checkpoint leaves opens a block.
            return DomainDerivationError::MalformedInputQueue;
        }
        auto const header = load_hub_word<InputHeaderWord>(word);
        size_t const length = header.payload_length.native();
        uint64_t const chunks = (length + sizeof(ChunkWord::payload) - 1) /
                                sizeof(ChunkWord::payload);
        if (head - position - 1 < chunks) {
            return DomainDerivationError::MalformedInputQueue;
        }
        byte_string payload;
        payload.reserve(length);
        for (uint64_t i = 0; i < chunks; ++i) {
            BOOST_OUTCOME_TRY(
                auto const chunk_word, queue.data_word(position + 1 + i));
            auto const chunk = load_hub_word<ChunkWord>(chunk_word);
            if (chunk.tag != CHUNK_TAG) {
                return DomainDerivationError::MalformedInputQueue;
            }
            payload.append(
                chunk.payload.data(),
                std::min(chunk.payload.size(), length - payload.size()));
        }
        BOOST_OUTCOME_TRY(
            auto input,
            decode_input(
                header.kind, load_be_field(header.fee), std::move(payload)));
        pending.blocks.back().inputs.push_back(std::move(input));
        position += 1 + chunks;
    }

    if (pending.blocks.empty()) {
        // The checkpoint covers the domain's latest block.
        pending.next_block = latest_block + 1;
    }
    else if (pending.next_block + pending.blocks.size() - 1 != latest_block) {
        return DomainDerivationError::MalformedInputQueue;
    }
    return std::optional{std::move(pending)};
}

MONAD_DOMAIN_NAMESPACE_END
