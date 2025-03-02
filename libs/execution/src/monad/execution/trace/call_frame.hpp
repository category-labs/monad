#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <cstdint>
#include <optional>

namespace evmone
{
    enum Opcode : uint8_t;
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

evmone::Opcode get_call_frame_opcode(CallType, uint32_t call_flags);

MONAD_NAMESPACE_END
