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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <cstdint>
#include <optional>
#include <vector>

namespace monad::vm::compiler
{
    enum EvmOpCode : uint8_t;
}

MONAD_NAMESPACE_BEGIN

enum class CallType
{
    CALL = 0,
    DELEGATECALL,
    CALLCODE,
    CREATE,
    CREATE2,
    SELFDESTRUCT,
};

struct CallFrame
{
    struct Log
    {
        Receipt::Log log;

        /*
         * The position field for a log is defined to be the number of sub-call
         * frames that happened in the same enclosing frame before the log event
         * was emitted. For example:
         *
         *   LOG  <- position 0
         *   CALL
         *   CALL
         *   LOG  <- position 2
         *   LOG  <- position 2
         *
         * Note that the last two logs have the same position; their relative
         * ordering is established by their position in the vector of log
         * output. Positions encode ordering between calls and logs, not between
         * logs.
         */
        size_t position;

        friend bool operator==(Log const &, Log const &) = default;
    };

    CallType type{};
    uint32_t flags{};
    Address from{};
    std::optional<Address> to{};
    uint256_t value{};
    uint64_t gas{};
    uint64_t gas_used{};
    byte_string input{};
    byte_string output{};
    evmc_status_code status{};
    uint64_t depth{};
    std::optional<std::vector<Log>> logs{};

    friend bool operator==(CallFrame const &, CallFrame const &) = default;
};

static_assert(sizeof(CallFrame) == 216);
static_assert(alignof(CallFrame) == 8);

nlohmann::json to_json(CallFrame const &);

vm::compiler::EvmOpCode get_call_frame_opcode(CallType, uint32_t call_flags);

MONAD_NAMESPACE_END
