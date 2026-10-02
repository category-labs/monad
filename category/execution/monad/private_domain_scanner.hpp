// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct PrivateDomainPayloadView
{
    size_t l1_transaction_index{};
    uint64_t domain_chain_id{};
    byte_string_view raw_payload{};
    uint64_t l1_gas_limit{};
};

struct DomainStateUpdate
{
    uint64_t domain_chain_id{};
    uint64_t domain_block_number{};
    bytes32_t new_state_root{};

    friend bool
    operator==(DomainStateUpdate const &, DomainStateUpdate const &) = default;
};

// One L1 -> domain message recorded on the hub. `source_chain_id`/`from` are
// the hub-authenticated origin: the L1 chain and its caller for an ordinary
// send, or the source domain and sender of a domain message the hub forwarded
// natively. A plaintext message carries its target and payload in the clear;
// an encrypted message carries `to || data` sealed to the domain viewing key
// in `payload`, so `to` is only known after decryption.
struct L1DomainMessage
{
    uint64_t domain_chain_id{};
    uint64_t source_chain_id{};
    Address from{};
    std::optional<Address> to{};
    byte_string payload{};
    uint256_t nonce{};
    bool encrypted{};
    size_t l1_transaction_index{};

    friend bool
    operator==(L1DomainMessage const &, L1DomainMessage const &) = default;
};

// private_domain_ids must be sorted and deduplicated.
Result<std::optional<PrivateDomainPayloadView>> extract_private_domain_payload(
    Transaction const &, uint256_t const &network_chain_id,
    Address const &sequencer_address,
    std::span<uint64_t const> private_domain_ids) noexcept;

// Scans synchronously. Returned payloads borrow storage from the outer L1
// transactions and must be consumed before those transactions are mutated.
std::vector<PrivateDomainPayloadView> scan_private_domain_payloads(
    std::span<Transaction const>, uint64_t block_number,
    uint256_t const &network_chain_id, Address const &sequencer_address,
    std::span<uint64_t const> private_domain_ids);

// Scans L1 receipts for DomainHub.DomainStateUpdated. Receipt blooms
// reject unrelated logs before they are visited. private_domain_ids must
// be sorted and deduplicated.
Result<std::vector<DomainStateUpdate>> scan_domain_state_updates(
    std::span<Receipt const>, Address const &domain_hub,
    std::span<uint64_t const> private_domain_ids) noexcept;

// Scans L1 receipts for DomainHub.L1MessageRecorded and
// DomainHub.EncryptedL1MessageRecorded. Messages are returned in receipt
// and log order, which is hub nonce order within a block. Receipt blooms
// reject unrelated logs before they are visited. private_domain_ids must
// be sorted and deduplicated.
Result<std::vector<L1DomainMessage>> scan_l1_domain_messages(
    std::span<Receipt const>, Address const &domain_hub,
    std::span<uint64_t const> private_domain_ids) noexcept;

MONAD_NAMESPACE_END
