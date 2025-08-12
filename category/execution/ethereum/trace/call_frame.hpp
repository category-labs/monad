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

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <cstdint>
#include <optional>

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

    friend bool operator==(CallFrame const &, CallFrame const &) = default;

    // TODO: official documentation doesn't contain "logs", but geth/reth
    // implementation does
};

static_assert(sizeof(CallFrame) == 184);
static_assert(alignof(CallFrame) == 8);

nlohmann::json to_json(CallFrame const &);

vm::compiler::EvmOpCode get_call_frame_opcode(CallType, uint32_t call_flags);

MONAD_NAMESPACE_END
