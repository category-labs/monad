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

#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/trace/call_frame.hpp>

#include <nlohmann/json.hpp>

MONAD_NAMESPACE_BEGIN

constexpr std::string_view call_kind_to_string(CallType const &type)
{
    switch (type) {
    case CallType::CALL:
        return "CALL";
    case CallType::DELEGATECALL:
        return "DELEGATECALL";
    case CallType::CALLCODE:
        return "CALLCODE";
    case CallType::CREATE:
        return "CREATE";
    case CallType::CREATE2:
        return "CREATE2";
    case CallType::SELFDESTRUCT:
        return "SELFDESTRUCT";
    default:
        MONAD_ASSERT(false);
    }
}

nlohmann::json to_json(CallFrame const &f)
{
    nlohmann::json res{};
    res["type"] = call_kind_to_string(f.type);
    if (MONAD_UNLIKELY(f.type == CallType::CALL && (f.flags & EVMC_STATIC))) {
        res["type"] = "STATICCALL";
    }
    res["from"] = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(f.from.bytes)), ""));
    if (f.to.has_value()) {
        res["to"] = fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(f.to.value().bytes)), ""));
    }
    res["value"] = "0x" + intx::to_string(f.value, 16);
    res["gas"] = fmt::format("0x{:x}", f.gas);
    res["gasUsed"] = fmt::format("0x{:x}", f.gas_used);
    res["input"] = "0x" + evmc::hex(f.input);
    res["output"] = "0x" + evmc::hex(f.output);

    // If status == EVMC_SUCCESS, no error field is shown
    if (f.status == EVMC_REVERT) {
        res["error"] = "REVERT";
    }
    else if (f.status != EVMC_SUCCESS) {
        res["error"] = "ERROR";
    }

    res["depth"] = f.depth; // needed for recursion
    res["calls"] = nlohmann::json::array();

    return res;
}

MONAD_NAMESPACE_END
