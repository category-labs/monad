// Copyright (C) 2025 Category Labs, Inc.
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
#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <chrono>
#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// Outcome of one EIP-7702 authorization entry, in transaction order:
/// 'd' = delegation applied, 'u' = undelegation applied, 'f' = the entry did
/// not fire. `authority` is empty when signature recovery failed.
struct TxAuthOutcome
{
    std::optional<Address> authority{};
    char outcome{'f'};
};

/// Per-transaction facts backing the `__tx` research log line, populated for
/// every merged transaction; `TxActivityLog` decides which lines are printed.
struct TxRecord
{
    uint32_t index{0};
    Address sender{};
    uint64_t nonce{0};
    uint256_t value{0};
    uint256_t balance_before{0};
    uint256_t balance_after{0};
    bool success{false};
    bool eligible{false};
    bool dipped{false};
    bool sender_delegated{false};
    std::vector<TxAuthOutcome> auths{};
};

struct BlockMetrics
{
    uint32_t num_retries{0};
    /// Reserve-balance stats, populated by `record_reserve_dip_metrics`:
    /// transactions whose sender was eligible to dip into its reserve, and
    /// successful transactions that the sender's allowed-dip exemption saved
    /// from a reserve-balance revert. Always zero for EVM traits and Monad
    /// revisions before MONAD_FOUR.
    uint32_t num_can_dip{0};
    uint32_t num_dipped{0};
    /// Transactions that merged with a failed receipt (reverted or otherwise
    /// unsuccessful execution).
    uint32_t num_reverted{0};
    /// Block-relative indices of the transactions counted in `num_dipped`,
    /// in block order (merges are serialized in transaction order).
    std::vector<uint32_t> dipped_tx_indices{};
    /// One record per merged transaction, in block order.
    std::vector<TxRecord> tx_records{};
    std::chrono::microseconds tx_exec_time{1};
};

MONAD_NAMESPACE_END
