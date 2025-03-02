#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/likely.h>
#include <monad/execution/trace/call_frame.hpp>

#include <evmone/instructions_opcodes.hpp>
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
    if (MONAD_UNLIKELY(f.type == CallType::CALL && f.flags == EVMC_STATIC)) {
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

evmone::Opcode get_call_frame_opcode(CallType type, uint32_t call_flags)
{
    using enum evmone::Opcode;
    switch (type) {
    case CallType::CALL:
        return call_flags & EVMC_STATIC ? OP_STATICCALL : OP_CALL;
    case CallType::CALLCODE:
        return OP_CALLCODE;
    case CallType::DELEGATECALL:
        return OP_DELEGATECALL;
    case CallType::CREATE:
        return OP_CREATE;
    case CallType::CREATE2:
        return OP_CREATE2;
    case CallType::SELFDESTRUCT:
        return OP_SELFDESTRUCT;
    }
    std::unreachable();
}

MONAD_NAMESPACE_END
