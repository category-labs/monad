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

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <cstdint>
#include <optional>
#include <span>

MONAD_NAMESPACE_BEGIN

struct CallFrame;
struct Receipt;
struct Transaction;

/// Record the transaction header events (TXN_HEADER_START, the EIP-2930
/// and EIP-7702 events, and TXN_HEADER_END), followed by the TXN_EVM_OUTPUT,
/// TXN_REJECT, or EVM_ERROR events, depending on what happened during
/// transaction execution; in the TXN_EVM_OUTPUT case, also record other
/// execution output events (TXN_LOG, TXN_CALL_FRAME, etc.)
void record_txn_events(
    uint32_t txn_num, Transaction const &, Address const &sender,
    std::span<std::optional<Address> const> authorities,
    Result<Receipt> const &, std::span<CallFrame const>);

MONAD_NAMESPACE_END
