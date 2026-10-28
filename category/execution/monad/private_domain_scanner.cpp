// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

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

constexpr monad::bytes32_t DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE =
    monad::abi_encode_event_signature(
        "DomainTransactionSequenced(uint64,bytes,uint256)");
static_assert(
    DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE ==
    0x840905264e95f5c327ec724710cb5708abafd6f5070886668d62fc66d4cf34dc_bytes32);

constexpr monad::bytes32_t DOMAIN_STATE_UPDATED_SIGNATURE =
    monad::abi_encode_event_signature(
        "DomainStateUpdated(uint64,uint256,uint64,bytes32,bytes32)");
static_assert(
    DOMAIN_STATE_UPDATED_SIGNATURE ==
    0x430254339a03e208e4f6cfb37d6928ba19f2f6315b1680dbecfba7e622f8c838_bytes32);

constexpr monad::bytes32_t L1_MESSAGE_RECORDED_SIGNATURE =
    monad::abi_encode_event_signature("L1MessageRecorded(uint64,uint64,address,"
                                      "address,bytes,uint256,uint256,bytes32)");
static_assert(
    L1_MESSAGE_RECORDED_SIGNATURE ==
    0x5407b49426d6ce93eaf2b804f06575113f1ce26f67ada45a1307db40662a528a_bytes32);

constexpr monad::bytes32_t ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE =
    monad::abi_encode_event_signature(
        "EncryptedL1MessageRecorded(uint64,uint64,address,bytes,uint256,"
        "uint256)");
static_assert(
    ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE ==
    0xb2679e875836e5ada3566e7b1304e7638ec7301653b9fbcb920dbe0aee7b4831_bytes32);

constexpr size_t ABI_WORD_SIZE = 32;
constexpr size_t DOMAIN_STATE_UPDATED_DATA_SIZE = 4 * ABI_WORD_SIZE;
// Indexed parameters including the signature topic.
constexpr size_t DOMAIN_TRANSACTION_SEQUENCED_TOPIC_COUNT = 2;
constexpr size_t L1_MESSAGE_RECORDED_TOPIC_COUNT = 4;
constexpr size_t ENCRYPTED_L1_MESSAGE_RECORDED_TOPIC_COUNT = 3;
constexpr size_t DOMAIN_TRANSACTION_SEQUENCED_HEAD_WORDS = 2;
constexpr size_t L1_MESSAGE_RECORDED_HEAD_WORDS = 5;
constexpr size_t ENCRYPTED_L1_MESSAGE_RECORDED_HEAD_WORDS = 4;

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

// Decodes the single dynamic `bytes` value that follows an event's head and
// must end its data: a length word, the bytes and canonical zero padding.
monad::Result<monad::byte_string>
decode_bytes_tail(monad::byte_string_view input)
{
    using namespace monad;

    BOOST_OUTCOME_TRY(auto const size_be, abi_decode_fixed<u256_be>(input));
    if (MONAD_UNLIKELY(size_be.native() > uint256_t{input.size()})) {
        return AbiDecodeError::InputTooShort;
    }
    size_t const size = static_cast<size_t>(size_be.native());
    byte_string payload{input.substr(0, size)};
    input.remove_prefix(size);

    size_t const padding_size =
        (ABI_WORD_SIZE - (size % ABI_WORD_SIZE)) % ABI_WORD_SIZE;
    if (MONAD_UNLIKELY(input.size() < padding_size)) {
        return AbiDecodeError::InputTooShort;
    }
    if (MONAD_UNLIKELY(!std::ranges::all_of(
            input.substr(0, padding_size),
            [](uint8_t const byte) { return byte == 0; }))) {
        return AbiDecodeError::InvalidEncoding;
    }
    input.remove_prefix(padding_size);
    if (MONAD_UNLIKELY(!input.empty())) {
        return AbiDecodeError::InputTooLong;
    }
    return payload;
}

// Solidity places an event's single dynamic value right after its head, so
// the offset word is fixed by the head size.
monad::Result<void> expect_tail_offset(
    monad::byte_string_view &input, size_t const head_word_count)
{
    using namespace monad;

    BOOST_OUTCOME_TRY(auto const offset, abi_decode_fixed<u256_be>(input));
    if (MONAD_UNLIKELY(
            offset.native() != uint256_t{head_word_count * ABI_WORD_SIZE})) {
        return AbiDecodeError::InvalidEncoding;
    }
    return outcome::success();
}

struct SequencedEventData
{
    monad::byte_string payload;
    monad::uint256_t fee;
};

// Non-indexed `(bytes payload, uint256 fee)`.
monad::Result<SequencedEventData>
decode_sequenced_event_data(monad::byte_string_view input)
{
    using namespace monad;

    BOOST_OUTCOME_TRY(expect_tail_offset(
        input, DOMAIN_TRANSACTION_SEQUENCED_HEAD_WORDS));
    BOOST_OUTCOME_TRY(auto const fee_be, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(auto payload, decode_bytes_tail(input));
    return SequencedEventData{
        .payload = std::move(payload), .fee = fee_be.native()};
}

struct MessageEventData
{
    uint64_t source_chain_id;
    monad::byte_string payload;
    monad::uint256_t nonce;
    monad::uint256_t fee;
};

// Non-indexed `(uint64 sourceChainId, bytes payload, uint256 nonce,
// uint256 fee[, bytes32 messageHash])`; the trailing hash is skipped.
monad::Result<MessageEventData> decode_message_event_data(
    monad::byte_string_view input, size_t const head_word_count)
{
    using namespace monad;

    BOOST_OUTCOME_TRY(
        auto const source_chain_id_be, abi_decode_fixed<u64_be>(input));
    BOOST_OUTCOME_TRY(expect_tail_offset(input, head_word_count));
    BOOST_OUTCOME_TRY(auto const nonce_be, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(auto const fee_be, abi_decode_fixed<u256_be>(input));
    constexpr size_t DECODED_HEAD_WORDS = 4;
    size_t const remaining_head =
        (head_word_count - DECODED_HEAD_WORDS) * ABI_WORD_SIZE;
    if (MONAD_UNLIKELY(input.size() < remaining_head)) {
        return AbiDecodeError::InputTooShort;
    }
    input.remove_prefix(remaining_head);
    BOOST_OUTCOME_TRY(auto payload, decode_bytes_tail(input));
    return MessageEventData{
        .source_chain_id = source_chain_id_be.native(),
        .payload = std::move(payload),
        .nonce = nonce_be.native(),
        .fee = fee_be.native()};
}

// Only events of served domains are decoded further, so a malformed event for
// another domain never affects this node.
monad::Result<std::optional<uint64_t>> served_domain_of(
    monad::Receipt::Log const &log,
    std::span<uint64_t const> const private_domain_ids)
{
    using namespace monad;

    if (MONAD_UNLIKELY(log.topics.size() < 2)) {
        return AbiDecodeError::InvalidEncoding;
    }
    auto domain_chain_id_word = to_byte_string_view(log.topics[1].bytes);
    BOOST_OUTCOME_TRY(
        auto const domain_chain_id_be,
        abi_decode_fixed<u64_be>(domain_chain_id_word));
    uint64_t const domain_chain_id = domain_chain_id_be.native();
    if (!std::ranges::contains(private_domain_ids, domain_chain_id)) {
        return std::optional<uint64_t>{};
    }
    return std::optional<uint64_t>{domain_chain_id};
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::vector<SequencedDomainTransaction>>
scan_sequenced_domain_transactions(
    std::span<Receipt const> const receipts, Address const &domain_hub,
    std::span<uint64_t const> const private_domain_ids) noexcept
{
    std::vector<SequencedDomainTransaction> transactions;
    if (private_domain_ids.empty()) {
        return transactions;
    }

    BloomProbe const hub_probe{to_byte_string_view(domain_hub.bytes)};
    BloomProbe const signature_probe{
        to_byte_string_view(DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE.bytes)};
    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &receipt = receipts[i];
        if (!hub_probe.matches(receipt.bloom) ||
            !signature_probe.matches(receipt.bloom)) {
            continue;
        }
        for (auto const &log : receipt.logs) {
            if (log.address != domain_hub || log.topics.empty() ||
                log.topics[0] != DOMAIN_TRANSACTION_SEQUENCED_SIGNATURE) {
                continue;
            }
            BOOST_OUTCOME_TRY(
                auto const domain_chain_id,
                served_domain_of(log, private_domain_ids));
            if (!domain_chain_id.has_value()) {
                continue;
            }
            if (MONAD_UNLIKELY(
                    log.topics.size() !=
                    DOMAIN_TRANSACTION_SEQUENCED_TOPIC_COUNT)) {
                return AbiDecodeError::InvalidEncoding;
            }
            BOOST_OUTCOME_TRY(
                auto event_data,
                decode_sequenced_event_data(byte_string_view{log.data}));
            transactions.push_back(SequencedDomainTransaction{
                .domain_chain_id = *domain_chain_id,
                .payload = std::move(event_data.payload),
                .fee = event_data.fee,
                .l1_transaction_index = i});
        }
    }
    return transactions;
}

Result<std::vector<DomainStateUpdate>> scan_domain_state_updates(
    std::span<Receipt const> const receipts, Address const &domain_hub,
    std::span<uint64_t const> const private_domain_ids) noexcept
{
    std::vector<DomainStateUpdate> updates;
    if (private_domain_ids.empty()) {
        return updates;
    }

    BloomProbe const hub_probe{to_byte_string_view(domain_hub.bytes)};
    BloomProbe const signature_probe{
        to_byte_string_view(DOMAIN_STATE_UPDATED_SIGNATURE.bytes)};
    for (auto const &receipt : receipts) {
        if (!hub_probe.matches(receipt.bloom) ||
            !signature_probe.matches(receipt.bloom)) {
            continue;
        }
        for (auto const &log : receipt.logs) {
            if (log.address != domain_hub || log.topics.empty() ||
                log.topics[0] != DOMAIN_STATE_UPDATED_SIGNATURE) {
                continue;
            }
            BOOST_OUTCOME_TRY(
                auto const domain_chain_id,
                served_domain_of(log, private_domain_ids));
            if (!domain_chain_id.has_value()) {
                continue;
            }
            if (MONAD_UNLIKELY(
                    log.topics.size() != 2 ||
                    log.data.size() != DOMAIN_STATE_UPDATED_DATA_SIZE)) {
                return AbiDecodeError::InvalidEncoding;
            }
            auto domain_block_number_word =
                byte_string_view{log.data}.substr(ABI_WORD_SIZE, ABI_WORD_SIZE);
            BOOST_OUTCOME_TRY(
                auto const domain_block_number_be,
                abi_decode_fixed<u64_be>(domain_block_number_word));
            uint64_t const domain_block_number =
                domain_block_number_be.native();

            bytes32_t new_state_root;
            std::ranges::copy(
                byte_string_view{log.data}.substr(
                    2 * ABI_WORD_SIZE, ABI_WORD_SIZE),
                new_state_root.bytes);
            updates.push_back(DomainStateUpdate{
                .domain_chain_id = *domain_chain_id,
                .domain_block_number = domain_block_number,
                .new_state_root = new_state_root});
        }
    }
    return updates;
}

Result<std::vector<L1DomainMessage>> scan_l1_domain_messages(
    std::span<Receipt const> const receipts, Address const &domain_hub,
    std::span<uint64_t const> const private_domain_ids) noexcept
{
    std::vector<L1DomainMessage> messages;
    if (private_domain_ids.empty()) {
        return messages;
    }

    BloomProbe const hub_probe{to_byte_string_view(domain_hub.bytes)};
    BloomProbe const plaintext_probe{
        to_byte_string_view(L1_MESSAGE_RECORDED_SIGNATURE.bytes)};
    BloomProbe const encrypted_probe{
        to_byte_string_view(ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE.bytes)};
    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &receipt = receipts[i];
        if (!hub_probe.matches(receipt.bloom) ||
            (!plaintext_probe.matches(receipt.bloom) &&
             !encrypted_probe.matches(receipt.bloom))) {
            continue;
        }
        for (auto const &log : receipt.logs) {
            if (log.address != domain_hub || log.topics.empty()) {
                continue;
            }
            bool encrypted;
            if (log.topics[0] == L1_MESSAGE_RECORDED_SIGNATURE) {
                encrypted = false;
            }
            else if (log.topics[0] == ENCRYPTED_L1_MESSAGE_RECORDED_SIGNATURE) {
                encrypted = true;
            }
            else {
                continue;
            }
            BOOST_OUTCOME_TRY(
                auto const domain_chain_id,
                served_domain_of(log, private_domain_ids));
            if (!domain_chain_id.has_value()) {
                continue;
            }
            size_t const topic_count =
                encrypted ? ENCRYPTED_L1_MESSAGE_RECORDED_TOPIC_COUNT
                          : L1_MESSAGE_RECORDED_TOPIC_COUNT;
            if (MONAD_UNLIKELY(log.topics.size() != topic_count)) {
                return AbiDecodeError::InvalidEncoding;
            }

            auto from_word = to_byte_string_view(log.topics[2].bytes);
            BOOST_OUTCOME_TRY(
                auto const from, abi_decode_fixed<Address>(from_word));
            std::optional<Address> to;
            if (!encrypted) {
                auto to_word = to_byte_string_view(log.topics[3].bytes);
                BOOST_OUTCOME_TRY(
                    auto const decoded_to, abi_decode_fixed<Address>(to_word));
                to = decoded_to;
            }
            BOOST_OUTCOME_TRY(
                auto event_data,
                decode_message_event_data(
                    byte_string_view{log.data},
                    encrypted ? ENCRYPTED_L1_MESSAGE_RECORDED_HEAD_WORDS
                              : L1_MESSAGE_RECORDED_HEAD_WORDS));
            messages.push_back(L1DomainMessage{
                .domain_chain_id = *domain_chain_id,
                .source_chain_id = event_data.source_chain_id,
                .from = from,
                .to = to,
                .payload = std::move(event_data.payload),
                .nonce = event_data.nonce,
                .fee = event_data.fee,
                .encrypted = encrypted,
                .l1_transaction_index = i});
        }
    }
    return messages;
}

MONAD_NAMESPACE_END
