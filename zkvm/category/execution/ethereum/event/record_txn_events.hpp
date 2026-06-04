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

// zkVM mirror — the host record_txn_events.cpp short-circuits when
// g_exec_event_recorder is null; the zkVM guest has no recorder, so the
// functions reduce to inline no-ops. Defining them inline here lets the
// surviving call sites in execute_transaction.cpp / execute_block_header.cpp
// link without the recorder / ring-buffer / ctypes-metadata machinery.

#pragma once

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <cstdint>
#include <optional>
#include <span>

enum monad_exec_account_access_context : uint8_t;

MONAD_NAMESPACE_BEGIN

struct CallFrame;
struct Receipt;
struct Transaction;

class State;

inline void record_txn_header_events(
    uint32_t, Transaction const &, Address const &,
    std::span<std::optional<Address> const>)
{
}

inline void record_txn_output_events(
    uint32_t, Receipt const &, std::span<CallFrame const>, State const &)
{
}

inline void
record_txn_error_event(uint32_t, Result<Receipt>::error_type const &)
{
}

inline void
record_account_access_events(monad_exec_account_access_context, State const &)
{
}

MONAD_NAMESPACE_END
