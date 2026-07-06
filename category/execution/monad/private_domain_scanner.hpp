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

MONAD_NAMESPACE_END
