#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/evm/execute.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/explicit_revision.hpp>
#include <monad/evm/status.hpp>
#include <monad/execution/baseline_execute.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmone/baseline.hpp>
#include <evmone/baseline_instruction_table.hpp>

#ifndef __clang__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored_attributes "clang::"
#endif
#include <evmone/execution_state.hpp>
#ifndef __clang__
    #pragma GCC diagnostic pop
#endif

#include <evmone/vm.hpp>

#ifdef EVMONE_TRACING
    #include <evmone/tracing.hpp>

    #include <quill/Quill.h>

    #include <sstream>
#endif

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <memory>

MONAD_NAMESPACE_BEGIN

evmc::Result baseline_execute(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    CodeAnalysis const &code_analysis)
{
    if (code_analysis.executable_code.empty()) {
        return evmc::Result{EVMC_SUCCESS, msg.gas};
    }

#ifdef EVMONE_TRACING
    std::ostringstream trace_ostream;
    vm.add_tracer(evmone::create_instruction_tracer(trace_ostream));
#endif

    auto const execution_state = std::make_unique<evmone::ExecutionState>(
        msg,
        rev,
        host->get_interface(),
        host->to_context(),
        code_analysis.executable_code,
        byte_string_view{});

    execution_state->analysis.baseline = &code_analysis;

    auto const &cost_table = evmone::baseline::get_baseline_cost_table(
        execution_state->rev, code_analysis.eof_header.version);

    evmone::VM vm{};
    auto const gas = evmone::baseline::monad_execute(
        vm.get_tracer(), msg.gas, *execution_state, cost_table, code_analysis);

    auto const gas_left = (execution_state->status == EVMC_SUCCESS ||
                           execution_state->status == EVMC_REVERT)
                              ? gas
                              : 0;
    auto const gas_refund = (execution_state->status == EVMC_SUCCESS)
                                ? execution_state->gas_refund
                                : 0;

    MONAD_ASSERT(
        execution_state->output_size != 0 ||
        execution_state->output_offset == 0);
    auto const result = evmc::make_result(
        execution_state->status,
        gas_left,
        gas_refund,
        execution_state->output_size != 0
            ? &execution_state->memory[execution_state->output_offset]
            : nullptr,
        execution_state->output_size);

    if (MONAD_UNLIKELY(vm.get_tracer() != nullptr)) {
        vm.get_tracer()->notify_execution_end(result);
    }

#ifdef EVMONE_TRACING
    LOG_TRACE_L1("{}", trace_ostream.str());
#endif

    return evmc::Result{result};
}

// TODO
template <evm::Revision rev>
evmc::Result monad_execute(
    State &state, BlockHeader const &header, byte_string_view const code,
    Address const &sender, // s
    Address const &origin, // o
    Address const &recipient, // r
    uint64_t const gas, // g
    uint256_t const &value, // v
    uint256_t const &gas_price, // p
    byte_string_view const input_data, // d
    size_t const depth, // e
    bool const can_modify_state // w
)
{
    using namespace monad::evm;

    if (code.empty()) {
        MONAD_ASSERT(gas <= std::numeric_limits<int64_t>::max());
        return evmc::Result{EVMC_SUCCESS, static_cast<int64_t>(gas)};
    }

    auto execution_state = std::make_shared<ExecutionState>(
        state,
        header,
        code,
        sender,
        origin,
        recipient,
        gas,
        value,
        gas_price,
        input_data,
        depth,
        can_modify_state);

    auto const status = execute<rev>(execution_state);

    auto const gas_left =
        (status == Status::Success || status == Status::Revert)
            ? execution_state->mstate.gas_left
            : 0;
    auto const gas_refund =
        (status == Status::Success) ? execution_state->gas_refund : 0;

    // TODO
    auto const evmc_status = [&] {
        switch (status) {
        case Status::Success:
            return EVMC_SUCCESS;
        case Status::OutOfGas:
            return EVMC_OUT_OF_GAS;
        case Status::InvalidMemoryAccess:
            return EVMC_INVALID_MEMORY_ACCESS;
        case Status::StaticModeViolation:
            return EVMC_STATIC_MODE_VIOLATION;
        case Status::BadJumpDest:
            return EVMC_BAD_JUMP_DESTINATION;
        case Status::Revert:
            return EVMC_REVERT;
        case Status::UndefinedInstruction:
            return EVMC_UNDEFINED_INSTRUCTION;
        case Status::StackOverflow:
            return EVMC_STACK_OVERFLOW;
        case Status::StackUnderflow:
            return EVMC_STACK_UNDERFLOW;
        case Status::PrecompileFailure:
            return EVMC_PRECOMPILE_FAILURE;
        case Status::InsufficientBalance:
            return EVMC_INSUFFICIENT_BALANCE;
        }
        MONAD_ASSERT(false);
    }();

    MONAD_ASSERT(gas_left <= std::numeric_limits<int64_t>::max());
    auto const result = evmc::make_result(
        evmc_status,
        static_cast<int64_t>(gas_left),
        gas_refund,
        execution_state->return_data.data(),
        execution_state->return_data.size());

    return evmc::Result{result};
}

EXPLICIT_REVISION(monad_execute);

MONAD_NAMESPACE_END
