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
#include <category/core/int.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>

MONAD_DOMAIN_NAMESPACE_BEGIN

// The words of the DomainHub's storage that the client reads, as the hub
// packs them: fields from the high bytes to the low bytes, integers
// big-endian. See InputQueue.sol in category-labs/monad-domains.

// A domain's latest block, the first word of its input queue: zero until the
// domain is registered.
struct LatestBlockWord
{
    u64_be gas_sold;
    u64_be input_words;
    u64_be l1_block_number;
    u64_be domain_block_number;
};

static_assert(sizeof(LatestBlockWord) == sizeof(bytes32_t));

// The queue's state, its second word: the entries the latest attested
// checkpoint does not cover are the data words [tail, head).
struct QueueStateWord
{
    u64_be message_count;
    u64_be first_period;
    u64_be tail;
    u64_be head;
};

static_assert(sizeof(QueueStateWord) == sizeof(bytes32_t));

// The first word of the entry that opens a domain block. `prevrandao` is the
// word after it.
struct BlockEntryWord
{
    uint8_t kind;
    u64_be l1_block_number;
    u64_be l1_timestamp;
    u64_be domain_block_number;
    // Zero if the L1 block has none.
    std::array<uint8_t, 7> slot_number;
};

static_assert(sizeof(BlockEntryWord) == sizeof(bytes32_t));

// The first word of an input. Its payload follows in chunks.
struct InputHeaderWord
{
    uint8_t kind;
    u32_be payload_length;
    std::array<uint8_t, 16> zero;
    // Wei paid for the input on L1.
    std::array<uint8_t, 11> fee;
};

static_assert(sizeof(InputHeaderWord) == sizeof(bytes32_t));

// A word of an input's payload, the last one zero-padded.
struct ChunkWord
{
    uint8_t tag;
    std::array<uint8_t, 31> payload;
};

static_assert(sizeof(ChunkWord) == sizeof(bytes32_t));

// What opens the payload of a message input, before the message's data.
struct MessagePayloadHeader
{
    u64_be source_chain_id;
    Address from;
    Address to;
    u64_be nonce;
};

static_assert(sizeof(MessagePayloadHeader) == 56);

// Reads the storage word `word` as a `Word`.
template <typename Word>
    requires(sizeof(Word) == sizeof(bytes32_t))
Word load_hub_word(bytes32_t const &word)
{
    return unaligned_load<Word>(word.bytes);
}

// The value of a big-endian field of N bytes, for the widths that have no
// integer type.
template <size_t N>
    requires(N <= sizeof(uint256_t))
uint256_t load_be_field(std::array<uint8_t, N> const &field)
{
    bytes32_t padded{};
    std::ranges::copy(field, padded.bytes + sizeof(padded.bytes) - N);
    return load_be<uint256_t>(padded.bytes);
}

MONAD_DOMAIN_NAMESPACE_END
