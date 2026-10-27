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

#include <category/execution/monad/private_domain_scanner.hpp>

#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr monad::bytes32_t DOMAIN_REGISTERED_SIGNATURE =
    monad::abi_encode_event_signature(
        "DomainRegistered(uint64,address,uint64)");
static_assert(
    DOMAIN_REGISTERED_SIGNATURE ==
    0x4d67e4de635f33a3a94b18cf726b1240bc94791b6b822e421b8c0902cddde3b7_bytes32);

constexpr monad::bytes32_t DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE =
    monad::abi_encode_event_signature(
        "DomainTransactionSequenced(uint64,bytes,uint256)");
static_assert(
    DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE ==
    0x840905264e95f5c327ec724710cb5708abafd6f5070886668d62fc66d4cf34dc_bytes32);

constexpr monad::bytes32_t L1_MESSAGE_RECORDED_SIGNATURE =
    monad::abi_encode_event_signature("L1MessageRecorded(uint64,uint64,address,"
                                      "address,bytes,uint256,uint256,bytes32)");
static_assert(
    L1_MESSAGE_RECORDED_SIGNATURE ==
    0x5407b49426d6ce93eaf2b804f06575113f1ce26f67ada45a1307db40662a528a_bytes32);

constexpr size_t ABI_WORD_SIZE = 32;

enum class HubEvent
{
    Registered,
    Sequenced,
    Message,
};

// Topic count, including the signature topic, and non-indexed head words of
// each event. DomainRegistered has no dynamic data, so its head is all of it.
struct EventLayout
{
    size_t topic_count;
    size_t head_words;
};

constexpr EventLayout layout(HubEvent const event)
{
    switch (event) {
    case HubEvent::Registered:
        // (checkpointInterval)
        return {.topic_count = 3, .head_words = 1};
    case HubEvent::Sequenced:
        // (offset(rlpTx), fee)
        return {.topic_count = 2, .head_words = 2};
    case HubEvent::Message:
        // (sourceChainId, offset(data), nonce, fee, messageHash)
        return {.topic_count = 4, .head_words = 5};
    }
    std::unreachable();
}

std::optional<HubEvent> classify(monad::bytes32_t const &topic)
{
    if (topic == DOMAIN_REGISTERED_SIGNATURE) {
        return HubEvent::Registered;
    }
    if (topic == DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE) {
        return HubEvent::Sequenced;
    }
    if (topic == L1_MESSAGE_RECORDED_SIGNATURE) {
        return HubEvent::Message;
    }
    return std::nullopt;
}

struct BloomProbe
{
    std::array<uint16_t, 3> bits;

    explicit BloomProbe(monad::byte_string_view const value)
    {
        auto const hash = monad::keccak256(value);
        for (size_t i = 0; i < bits.size(); ++i) {
            bits[i] =
                monad::load_be_unsafe<uint16_t>(hash.bytes + i * 2) & 2047u;
        }
    }

    bool matches(monad::Receipt::Bloom const &bloom) const noexcept
    {
        return std::ranges::all_of(bits, [&](uint16_t const bit) {
            return (bloom[255u - bit / 8u] & (1u << (bit & 7u))) != 0;
        });
    }
};

monad::byte_string_view
word(monad::byte_string_view const data, size_t const index)
{
    return data.substr(index * ABI_WORD_SIZE, ABI_WORD_SIZE);
}

template <typename T>
monad::Result<T> decode_word(monad::byte_string_view const data, size_t index)
{
    auto input = word(data, index);
    return monad::abi_decode_fixed<T>(input);
}

// Decodes the single `bytes` member of an event's data, whose offset is head
// word `offset_index`. Solidity places it right after the head, followed by
// zero padding to a word boundary and nothing else.
monad::Result<monad::byte_string> decode_bytes_member(
    monad::byte_string_view const data, size_t const head_words,
    size_t const offset_index)
{
    using namespace monad;

    size_t const head_size = head_words * ABI_WORD_SIZE;
    BOOST_OUTCOME_TRY(
        auto const offset, decode_word<u256_be>(data, offset_index));
    if (MONAD_UNLIKELY(offset.native() != uint256_t{head_size})) {
        return AbiDecodeError::InvalidEncoding;
    }
    byte_string_view tail = data.substr(head_size);
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

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<DomainHubEvents> scan_domain_hub_events(
    std::span<Receipt const> const receipts, Address const &domain_hub,
    std::span<uint64_t const> const domain_ids)
{
    DomainHubEvents events;
    if (domain_ids.empty()) {
        return events;
    }

    BloomProbe const hub_probe{to_byte_string_view(domain_hub.bytes)};
    std::array const signature_probes{
        BloomProbe{to_byte_string_view(DOMAIN_REGISTERED_SIGNATURE.bytes)},
        BloomProbe{
            to_byte_string_view(DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE.bytes)},
        BloomProbe{to_byte_string_view(L1_MESSAGE_RECORDED_SIGNATURE.bytes)},
    };

    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &receipt = receipts[i];
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
            auto const event = classify(log.topics[0]);
            if (!event.has_value()) {
                continue;
            }
            // Every hub event indexes the domain first.
            if (MONAD_UNLIKELY(log.topics.size() < 2)) {
                return AbiDecodeError::InvalidEncoding;
            }
            BOOST_OUTCOME_TRY(
                auto const domain_chain_id_be,
                decode_word<u64_be>(
                    to_byte_string_view(log.topics[1].bytes), 0));
            uint64_t const domain_chain_id = domain_chain_id_be.native();
            if (!std::ranges::binary_search(domain_ids, domain_chain_id)) {
                continue;
            }

            auto const [topic_count, head_words] = layout(*event);
            byte_string_view const data{log.data};
            if (MONAD_UNLIKELY(
                    log.topics.size() != topic_count ||
                    data.size() < head_words * ABI_WORD_SIZE)) {
                return AbiDecodeError::InvalidEncoding;
            }

            switch (*event) {
            case HubEvent::Registered:
                if (MONAD_UNLIKELY(data.size() != head_words * ABI_WORD_SIZE)) {
                    return AbiDecodeError::InvalidEncoding;
                }
                events.registered_domains.push_back(domain_chain_id);
                break;
            case HubEvent::Sequenced: {
                BOOST_OUTCOME_TRY(
                    auto const fee, decode_word<u256_be>(data, 1));
                BOOST_OUTCOME_TRY(
                    auto payload, decode_bytes_member(data, head_words, 0));
                events.sequenced.push_back(SequencedDomainPayload{
                    .domain_chain_id = domain_chain_id,
                    .l1_transaction_index = i,
                    .payload = std::move(payload),
                    .fee = fee.native()});
                break;
            }
            case HubEvent::Message: {
                BOOST_OUTCOME_TRY(
                    auto const from,
                    decode_word<Address>(
                        to_byte_string_view(log.topics[2].bytes), 0));
                BOOST_OUTCOME_TRY(
                    auto const to,
                    decode_word<Address>(
                        to_byte_string_view(log.topics[3].bytes), 0));
                BOOST_OUTCOME_TRY(
                    auto const source_chain_id, decode_word<u64_be>(data, 0));
                BOOST_OUTCOME_TRY(
                    auto const nonce, decode_word<u256_be>(data, 2));
                BOOST_OUTCOME_TRY(
                    auto const fee, decode_word<u256_be>(data, 3));
                BOOST_OUTCOME_TRY(
                    auto message_data,
                    decode_bytes_member(data, head_words, 1));
                events.messages.push_back(L1DomainMessage{
                    .domain_chain_id = domain_chain_id,
                    .source_chain_id = source_chain_id.native(),
                    .from = from,
                    .to = to,
                    .data = std::move(message_data),
                    .nonce = nonce.native(),
                    .fee = fee.native(),
                    .l1_transaction_index = i});
                break;
            }
            }
        }
    }
    return events;
}

MONAD_NAMESPACE_END
