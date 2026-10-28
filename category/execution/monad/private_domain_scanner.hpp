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

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

// One DomainTransactionSequenced event: `payload` is the HPKE-sealed signed
// transaction, `fee` the wei paid for it.
struct SequencedDomainTransaction
{
    uint64_t domain_chain_id{};
    byte_string payload{};
    uint256_t fee{};
    size_t l1_transaction_index{};

    friend bool operator==(
        SequencedDomainTransaction const &,
        SequencedDomainTransaction const &) = default;
};

struct DomainStateUpdate
{
    uint64_t domain_chain_id{};
    uint64_t domain_block_number{};
    bytes32_t new_state_root{};

    friend bool
    operator==(DomainStateUpdate const &, DomainStateUpdate const &) = default;
};

// One (Encrypted)L1MessageRecorded event. `source_chain_id`/`from` are the
// hub-authenticated origin. An encrypted `payload` is `to || data` sealed to
// the domain viewing key, so `to` is unset until decryption.
struct L1DomainMessage
{
    uint64_t domain_chain_id{};
    uint64_t source_chain_id{};
    Address from{};
    std::optional<Address> to{};
    byte_string payload{};
    uint256_t nonce{};
    uint256_t fee{};
    bool encrypted{};
    size_t l1_transaction_index{};

    friend bool
    operator==(L1DomainMessage const &, L1DomainMessage const &) = default;
};

// DomainTransactionSequenced events of the served domains in receipt and log
// order; a reverted sequencing call emits none.
Result<std::vector<SequencedDomainTransaction>>
scan_sequenced_domain_transactions(
    std::span<Receipt const>, Address const &domain_hub,
    std::span<uint64_t const> private_domain_ids) noexcept;

// DomainStateUpdated events of the served domains.
Result<std::vector<DomainStateUpdate>> scan_domain_state_updates(
    std::span<Receipt const>, Address const &domain_hub,
    std::span<uint64_t const> private_domain_ids) noexcept;

// L1MessageRecorded and EncryptedL1MessageRecorded events of the served
// domains in receipt and log order, which is hub nonce order within a block.
Result<std::vector<L1DomainMessage>> scan_l1_domain_messages(
    std::span<Receipt const>, Address const &domain_hub,
    std::span<uint64_t const> private_domain_ids) noexcept;

MONAD_NAMESPACE_END
