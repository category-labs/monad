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

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/scan_domain_inputs.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_BEGIN

constexpr bytes32_t DOMAIN_REGISTERED_SIGNATURE =
    abi_encode_event_signature("DomainRegistered(uint64,address,uint64)");
static_assert(
    DOMAIN_REGISTERED_SIGNATURE ==
    0x4d67e4de635f33a3a94b18cf726b1240bc94791b6b822e421b8c0902cddde3b7_bytes32);

constexpr bytes32_t DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE =
    abi_encode_event_signature(
        "DomainTransactionSequenced(uint64,bytes,uint256)");
static_assert(
    DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE ==
    0x840905264e95f5c327ec724710cb5708abafd6f5070886668d62fc66d4cf34dc_bytes32);

constexpr bytes32_t L1_MESSAGE_RECORDED_SIGNATURE =
    abi_encode_event_signature("L1MessageRecorded(uint64,uint64,address,"
                               "address,bytes,uint256,uint256,bytes32)");
static_assert(
    L1_MESSAGE_RECORDED_SIGNATURE ==
    0x5407b49426d6ce93eaf2b804f06575113f1ce26f67ada45a1307db40662a528a_bytes32);

constexpr bytes32_t ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE =
    abi_encode_event_signature("EncryptedL1MessageRecorded(uint64,"
                               "uint64,address,bytes,uint256,uint256)");
static_assert(
    ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE ==
    0xb2679e875836e5ada3566e7b1304e7638ec7301653b9fbcb920dbe0aee7b4831_bytes32);

constexpr size_t ABI_WORD_SIZE = 32;

enum class HubEvent
{
    DomainRegistered,
    TransactionSequenced,
    MessageRecorded,
    EncryptedMessageRecorded,
};

// The shape of the log of one DomainHub event. A log holds the event's
// signature and indexed parameters as topics, and its other parameters
// ABI-encoded as data: a head of one 32-byte word per parameter, then the
// bytes of the dynamic parameter, whose head word is its offset.
struct HubEventSpec
{
    HubEvent event;
    bytes32_t signature;
    size_t topic_count;
    size_t head_words;
};

constexpr std::array HUB_EVENTS{
    // topics: signature, domainChainId, feeRecipient
    // head:   checkpointInterval
    HubEventSpec{
        .event = HubEvent::DomainRegistered,
        .signature = DOMAIN_REGISTERED_SIGNATURE,
        .topic_count = 3,
        .head_words = 1},
    // topics: signature, domainChainId
    // head:   offset(rlpTx), fee
    HubEventSpec{
        .event = HubEvent::TransactionSequenced,
        .signature = DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE,
        .topic_count = 2,
        .head_words = 2},
    // topics: signature, domainChainId, from, to
    // head:   sourceChainId, offset(data), nonce, fee, messageHash
    HubEventSpec{
        .event = HubEvent::MessageRecorded,
        .signature = L1_MESSAGE_RECORDED_SIGNATURE,
        .topic_count = 4,
        .head_words = 5},
    // topics: signature, domainChainId, from
    // head:   sourceChainId, offset(ciphertext), nonce, fee
    HubEventSpec{
        .event = HubEvent::EncryptedMessageRecorded,
        .signature = ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE,
        .topic_count = 3,
        .head_words = 4},
};

// The hub event with this signature topic, null if it is not one of
// HUB_EVENTS.
HubEventSpec const *find_hub_event(bytes32_t const &signature_topic)
{
    auto const it = std::ranges::find_if(HUB_EVENTS, [&](auto const &spec) {
        return spec.signature == signature_topic;
    });
    return it == HUB_EVENTS.end() ? nullptr : &*it;
}

struct BloomProbe
{
    std::array<uint16_t, 3> bits;

    explicit BloomProbe(byte_string_view const value)
    {
        auto const hash = keccak256(value);
        for (size_t i = 0; i < bits.size(); ++i) {
            bits[i] = load_be_unsafe<uint16_t>(hash.bytes + i * 2) & 2047u;
        }
    }

    bool matches(Receipt::Bloom const &bloom) const noexcept
    {
        return std::ranges::all_of(bits, [&](uint16_t const bit) {
            return (bloom[255u - bit / 8u] & (1u << (bit & 7u))) != 0;
        });
    }
};

// Decodes word `index` of `data`
template <typename T>
Result<T> abi_decode_word(byte_string_view const data, size_t const index)
{
    MONAD_ASSERT(data.size() >= (index + 1) * ABI_WORD_SIZE);
    auto input = data.substr(index * ABI_WORD_SIZE, ABI_WORD_SIZE);
    return abi_decode_fixed<T>(input);
}

// Decodes the one `bytes` parameter of an event from its log's data, which
// must hold the whole head. Head word `offset_index` is the parameter's
// offset. Solidity places the parameter right after the head, followed by
// zero padding to a word boundary and nothing else.
Result<byte_string> abi_decode_event_bytes(
    byte_string_view const log_data, size_t const head_words,
    size_t const offset_index)
{
    size_t const head_size = head_words * ABI_WORD_SIZE;
    MONAD_ASSERT(offset_index < head_words && log_data.size() >= head_size);
    BOOST_OUTCOME_TRY(
        auto const offset, abi_decode_word<u256_be>(log_data, offset_index));
    if (MONAD_UNLIKELY(offset.native() != uint256_t{head_size})) {
        return AbiDecodeError::InvalidEncoding;
    }
    byte_string_view tail = log_data.substr(head_size);
    BOOST_OUTCOME_TRY(auto const size_be, abi_decode_fixed<u256_be>(tail));
    if (MONAD_UNLIKELY(size_be.native() > uint256_t{tail.size()})) {
        return AbiDecodeError::InputTooShort;
    }
    size_t const size = static_cast<size_t>(size_be.native());
    size_t const padded_size =
        (size + ABI_WORD_SIZE - 1) / ABI_WORD_SIZE * ABI_WORD_SIZE;
    if (MONAD_UNLIKELY(tail.size() < padded_size)) {
        return AbiDecodeError::InputTooShort;
    }
    if (MONAD_UNLIKELY(tail.size() > padded_size)) {
        return AbiDecodeError::InputTooLong;
    }
    if (MONAD_UNLIKELY(!std::ranges::all_of(
            tail.substr(size), [](uint8_t const b) { return b == 0; }))) {
        return AbiDecodeError::InvalidEncoding;
    }
    return byte_string{tail.substr(0, size)};
}

// Decodes one hub event of the domain from its log and adds it to `inputs`.
Result<void> add_hub_event(
    HubEventSpec const &spec, Receipt::Log const &log, DomainInputs &inputs)
{
    size_t const head_words = spec.head_words;
    byte_string_view const log_data{log.data};
    if (MONAD_UNLIKELY(
            log.topics.size() != spec.topic_count ||
            log_data.size() < head_words * ABI_WORD_SIZE)) {
        return AbiDecodeError::InvalidEncoding;
    }

    switch (spec.event) {
    case HubEvent::DomainRegistered:
        if (MONAD_UNLIKELY(log_data.size() != head_words * ABI_WORD_SIZE)) {
            return AbiDecodeError::InvalidEncoding;
        }
        inputs.registered = true;
        break;
    case HubEvent::TransactionSequenced: {
        BOOST_OUTCOME_TRY(
            auto const fee, abi_decode_word<u256_be>(log_data, 1));
        BOOST_OUTCOME_TRY(
            auto payload, abi_decode_event_bytes(log_data, head_words, 0));
        inputs.inputs.emplace_back(SequencedDomainPayload{
            .payload = std::move(payload), .fee = fee.native()});
        break;
    }
    case HubEvent::MessageRecorded: {
        BOOST_OUTCOME_TRY(
            auto const from,
            abi_decode_word<Address>(
                to_byte_string_view(log.topics[2].bytes), 0));
        BOOST_OUTCOME_TRY(
            auto const to,
            abi_decode_word<Address>(
                to_byte_string_view(log.topics[3].bytes), 0));
        BOOST_OUTCOME_TRY(
            auto const source_chain_id, abi_decode_word<u64_be>(log_data, 0));
        BOOST_OUTCOME_TRY(
            auto const nonce, abi_decode_word<u256_be>(log_data, 2));
        BOOST_OUTCOME_TRY(
            auto const fee, abi_decode_word<u256_be>(log_data, 3));
        BOOST_OUTCOME_TRY(
            auto message_data, abi_decode_event_bytes(log_data, head_words, 1));
        inputs.inputs.emplace_back(L1DomainMessage{
            .source_chain_id = source_chain_id.native(),
            .from = from,
            .to = to,
            .data = std::move(message_data),
            .nonce = nonce.native(),
            .fee = fee.native()});
        break;
    }
    case HubEvent::EncryptedMessageRecorded:
        // Only checked: this version delivers none.
        BOOST_OUTCOME_TRYV(abi_decode_event_bytes(log_data, head_words, 1));
        inputs.inputs.emplace_back(EncryptedL1DomainMessage{});
        break;
    }
    return outcome::success();
}

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

bool may_have_domain_inputs(
    BlockHeader const &l1_header, Address const &domain_hub,
    uint64_t const domain_chain_id)
{
    // Every hub event of the domain is logged by the hub and carries the
    // domain's chain id as its first indexed parameter.
    auto const domain_topic = abi_encode_uint(u64_be{domain_chain_id});
    return BloomProbe{to_byte_string_view(domain_hub.bytes)}.matches(
               l1_header.logs_bloom) &&
           BloomProbe{to_byte_string_view(domain_topic.bytes)}.matches(
               l1_header.logs_bloom);
}

Result<DomainInputs> scan_domain_inputs(
    BlockHeader const &l1_header, std::span<Receipt const> const receipts,
    Address const &domain_hub, uint64_t const domain_chain_id)
{
    DomainInputs inputs{
        .l1_block_number = l1_header.number,
        .timestamp = l1_header.timestamp,
        .prev_randao = l1_header.prev_randao,
        .slot_number = l1_header.slot_number};

    bytes32_t const domain_topic = abi_encode_uint(u64_be{domain_chain_id});
    BloomProbe const hub_probe{to_byte_string_view(domain_hub.bytes)};
    static std::array const signature_probes{
        BloomProbe{to_byte_string_view(DOMAIN_REGISTERED_SIGNATURE.bytes)},
        BloomProbe{
            to_byte_string_view(DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE.bytes)},
        BloomProbe{to_byte_string_view(L1_MESSAGE_RECORDED_SIGNATURE.bytes)},
        BloomProbe{
            to_byte_string_view(ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE.bytes)},
    };

    for (auto const &receipt : receipts) {
        if (!hub_probe.matches(receipt.bloom) ||
            std::ranges::none_of(signature_probes, [&](auto const &probe) {
                return probe.matches(receipt.bloom);
            })) {
            continue;
        }
        for (auto const &log : receipt.logs) {
            if (log.address != domain_hub || log.topics.empty()) {
                continue;
            }
            auto const *const spec = find_hub_event(log.topics[0]);
            if (spec == nullptr) {
                continue;
            }
            // Every hub event indexes the domain first.
            if (MONAD_UNLIKELY(log.topics.size() < 2)) {
                return AbiDecodeError::InvalidEncoding;
            }
            if (log.topics[1] != domain_topic) {
                continue;
            }

            BOOST_OUTCOME_TRYV(add_hub_event(*spec, log, inputs));
        }
    }
    return inputs;
}

MONAD_DOMAIN_NAMESPACE_END
