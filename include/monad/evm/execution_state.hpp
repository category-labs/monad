#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/evm/code_analysis.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_environment.hpp>
#include <monad/evm/machine_state.hpp>
#include <monad/evm/system_state.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class State;
struct BlockHeader;

MONAD_NAMESPACE_END

MONAD_EVM_NAMESPACE_BEGIN

struct CallParameters;

struct ExecutionState
{
    ExecutionEnvironment env;
    MachineState mstate;
    SystemState sstate;

    byte_string last_return_data; // H_return from last executed subcontext.
                                  // TODO: keep around subcontext?
    byte_string return_data; // H_return
    int64_t gas_refund; // TODO: move this to accrued substate (as defined
                        // in YP)?
    CodeAnalysis analysis;

    ExecutionState(
        State &, BlockHeader const &, byte_string_view code,
        Address const &sender, // s
        Address const &origin, // o
        Address const &recipient, // r
        uint64_t const gas, // g
        uint256_t const &value, // v
        uint256_t const &gas_price, // p
        byte_string_view input_data, // d
        size_t depth, // e
        bool can_modify_state // w
    );

    ExecutionState(State &, BlockHeader const &, CallParameters const &);
};

static_assert(sizeof(ExecutionState) == 33160);
static_assert(alignof(ExecutionState) == 8);

MONAD_EVM_NAMESPACE_END
