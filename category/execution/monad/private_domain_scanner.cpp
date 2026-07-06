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
#include <category/core/log.hpp>
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
#include <string>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct FunctionSelector
{
    static constexpr uint32_t SEQUENCE_TO_DOMAIN =
        monad::abi_encode_selector("sequenceToDomain(uint64,bytes)");
};

constexpr monad::bytes32_t DOMAIN_STATE_UPDATED_SIGNATURE =
    monad::abi_encode_event_signature(
        "DomainStateUpdated(uint64,uint256,uint64,bytes32,bytes32)");
static_assert(
    DOMAIN_STATE_UPDATED_SIGNATURE ==
    0x430254339a03e208e4f6cfb37d6928ba19f2f6315b1680dbecfba7e622f8c838_bytes32);

static_assert(FunctionSelector::SEQUENCE_TO_DOMAIN == 0xc791e98a);

constexpr size_t ABI_WORD_SIZE = 32;
constexpr size_t UINT64_PADDING_SIZE = ABI_WORD_SIZE - sizeof(uint64_t);
constexpr uint64_t PAYLOAD_OFFSET = 2 * ABI_WORD_SIZE;
constexpr size_t DOMAIN_STATE_UPDATED_DATA_SIZE = 4 * ABI_WORD_SIZE;

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

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::optional<PrivateDomainPayloadView>> extract_private_domain_payload(
    Transaction const &tx, uint256_t const &network_chain_id,
    Address const &sequencer_address,
    std::span<uint64_t const> const private_domain_ids) noexcept
{
    // Reject unrelated outer transactions before inspecting calldata.
    if (private_domain_ids.empty() || !tx.to.has_value() ||
        *tx.to != sequencer_address || !tx.sc.chain_id.has_value() ||
        *tx.sc.chain_id != network_chain_id) {
        return std::optional<PrivateDomainPayloadView>{};
    }

    // A matching call begins with the canonical Solidity function selector.
    byte_string_view input{tx.data};
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return std::optional<PrivateDomainPayloadView>{};
    }

    auto const signature = load_be_unsafe<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);
    if (signature != FunctionSelector::SEQUENCE_TO_DOMAIN) {
        return std::optional<PrivateDomainPayloadView>{};
    }

    // Decode the canonical ABI head: a zero-padded uint64 followed by the
    // dynamic bytes offset. Solidity emits the bytes tail at offset 64.
    if (MONAD_UNLIKELY(input.size() < ABI_WORD_SIZE)) {
        return AbiDecodeError::InputTooShort;
    }
    if (MONAD_UNLIKELY(!std::ranges::all_of(
            input.substr(0, UINT64_PADDING_SIZE),
            [](uint8_t const byte) { return byte == 0; }))) {
        return AbiDecodeError::InvalidEncoding;
    }

    BOOST_OUTCOME_TRY(
        auto const domain_chain_id_be, abi_decode_fixed<u64_be>(input));
    uint64_t const domain_chain_id = domain_chain_id_be.native();

    // Ignore calls for domains not assigned to this node before decoding
    // the dynamic payload.
    if (!std::ranges::contains(private_domain_ids, domain_chain_id)) {
        return std::optional<PrivateDomainPayloadView>{};
    }

    BOOST_OUTCOME_TRY(
        auto const payload_offset, abi_decode_fixed<u256_be>(input));
    if (MONAD_UNLIKELY(payload_offset.native() != PAYLOAD_OFFSET)) {
        return AbiDecodeError::InvalidEncoding;
    }

    // Decode the bytes tail in place. The returned view borrows from tx.data;
    // canonical Solidity encoding has zero padding and no trailing calldata.
    BOOST_OUTCOME_TRY(
        auto const payload_size_be, abi_decode_fixed<u256_be>(input));
    if (MONAD_UNLIKELY(payload_size_be.native() > uint256_t{input.size()})) {
        return AbiDecodeError::InputTooShort;
    }

    size_t const payload_size = static_cast<size_t>(payload_size_be.native());
    byte_string_view const raw_payload = input.substr(0, payload_size);
    input.remove_prefix(payload_size);

    size_t const padding_size =
        (ABI_WORD_SIZE - (payload_size % ABI_WORD_SIZE)) % ABI_WORD_SIZE;
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

    return std::optional<PrivateDomainPayloadView>{PrivateDomainPayloadView{
        .l1_transaction_index = 0,
        .domain_chain_id = domain_chain_id,
        .raw_payload = raw_payload,
        .l1_gas_limit = tx.gas_limit}};
}

std::vector<PrivateDomainPayloadView> scan_private_domain_payloads(
    std::span<Transaction const> const transactions,
    uint64_t const block_number, uint256_t const &network_chain_id,
    Address const &sequencer_address,
    std::span<uint64_t const> const private_domain_ids)
{
    if (private_domain_ids.empty()) {
        return {};
    }

    std::vector<PrivateDomainPayloadView> payloads;

    size_t malformed_count = 0;
    size_t first_malformed_index = 0;
    std::string first_error;

    auto const record_error =
        [&]<typename Error>(size_t const index, Error const &error) {
            if (malformed_count++ == 0) {
                first_malformed_index = index;
                first_error = error.message().c_str();
            }
        };

    for (size_t i = 0; i < transactions.size(); ++i) {
        auto result = extract_private_domain_payload(
            transactions[i],
            network_chain_id,
            sequencer_address,
            private_domain_ids);
        if (MONAD_UNLIKELY(result.has_error())) {
            record_error(i, result.assume_error());
        }
        else if (result.value().has_value()) {
            auto payload = *result.value();
            payload.l1_transaction_index = i;
            payloads.push_back(payload);
        }
    }

    if (malformed_count != 0) {
        LOG_WARNING(
            "Dropped {} malformed private domain sequencing call(s) in "
            "block {}; first at transaction {}: {}",
            malformed_count,
            block_number,
            first_malformed_index,
            first_error);
    }
    return payloads;
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
            if (MONAD_UNLIKELY(log.topics.size() != 2)) {
                return AbiDecodeError::InvalidEncoding;
            }

            auto domain_chain_id_word =
                to_byte_string_view(log.topics[1].bytes);
            BOOST_OUTCOME_TRY(
                auto const domain_chain_id_be,
                abi_decode_fixed<u64_be>(domain_chain_id_word));
            uint64_t const domain_chain_id = domain_chain_id_be.native();
            if (!std::ranges::contains(private_domain_ids, domain_chain_id)) {
                continue;
            }
            if (MONAD_UNLIKELY(
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
                .domain_chain_id = domain_chain_id,
                .domain_block_number = domain_block_number,
                .new_state_root = new_state_root});
        }
    }
    return updates;
}

MONAD_NAMESPACE_END
