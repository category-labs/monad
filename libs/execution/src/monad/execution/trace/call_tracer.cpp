#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/trace/call_tracer.hpp>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>

#include <fstream>
#include <iomanip>
#include <optional>
#include <span>
#include <sstream>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

std::string_view call_kind_to_string(CallKind const &type)
{
    switch (type) {
    case CallKind::CALL:
        return "CALL";
    case CallKind::DELEGATECALL:
        return "DELEGATECALL";
    case CallKind::CALLCODE:
        return "CALLCODE";
    case CallKind::CREATE:
        return "CREATE";
    case CallKind::CREATE2:
        return "CREATE2";
    case CallKind::SELFDESTRUCT:
        return "SELFDESTRUCT";
    default:
        MONAD_ASSERT(false);
    }
}

nlohmann::json CallFrame::to_json() const
{
    nlohmann::json res{};
    res["type"] = call_kind_to_string(type);
    if (MONAD_UNLIKELY(type == CallKind::CALL && flags == 1)) {
        res["type"] = "STATICCALL";
    }
    res["from"] = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(from.bytes)), ""));
    if (to.has_value()) {
        res["to"] = fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(to.value().bytes)), ""));
    }
    res["value"] = "0x" + intx::to_string(value, 16);
    res["gas"] = fmt::format("0x{:x}", gas);
    res["gasUsed"] = fmt::format("0x{:x}", gas_used);
    res["input"] = "0x" + evmc::hex(input);
    res["output"] = "0x" + evmc::hex(output);

    // If status == EVMC_SUCCESS, no error field is shown
    if (status == EVMC_REVERT) {
        res["error"] = "REVERT";
    }
    else if (status != EVMC_SUCCESS) {
        res["error"] = "ERROR";
    }

    res["depth"] = depth; // needed for recursion
    res["calls"] = nlohmann::json::array();

    return res;
}

CallTracer::CallTracer(Transaction const &tx)
    : call_frames_{}
    , depth_{0}
    , tx_(tx)
    , tx_hash_(keccak256(rlp::encode_transaction(tx)))
{
}

void CallTracer::to_json_helper(nlohmann::json &json, size_t &pos)
{
    if (pos >= call_frames_.size()) {
        return;
    }
    json = call_frames_[pos].to_json();

    while (pos + 1 < call_frames_.size()) {
        MONAD_ASSERT(json.contains("depth"));
        if (call_frames_[pos + 1].depth > json["depth"]) {
            nlohmann::json j;
            pos++;
            to_json_helper(j, pos);
            json["calls"].push_back(j);
        }
        else {
            return;
        }
    }
}

nlohmann::json CallTracer::to_json()
{
    MONAD_ASSERT(!call_frames_.empty());
    MONAD_ASSERT(call_frames_[0].depth == 0);

    size_t pos = 0;

    nlohmann::json res{};
    auto const key = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(tx_hash_.bytes)), ""));
    nlohmann::json value{};
    to_json_helper(value, pos);
    res[key] = value;

    return res;
}

MONAD_NAMESPACE_END
