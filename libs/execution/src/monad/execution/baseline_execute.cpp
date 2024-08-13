#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/execution/baseline_execute.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmone/baseline.hpp>

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

    evmone::VM vm{};

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

    auto const result =
        evmone::baseline::execute(vm, msg.gas, *execution_state, code_analysis);

    #ifdef EVMONE_TRACING
        LOG_TRACE_L1("{}", trace_ostream.str());
    #endif

    return evmc::Result{result};
}

MONAD_NAMESPACE_END
