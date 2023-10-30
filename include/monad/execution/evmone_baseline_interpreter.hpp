#pragma once

#include <monad/config.hpp>

#include <monad/core/byte_string.hpp>

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

#include <memory>

MONAD_NAMESPACE_BEGIN

template <class TState, class Traits>
struct EVMOneBaselineInterpreter
{
    template <class TEvmHost>
    static evmc::Result
    execute(TEvmHost *host, evmc_message const &msg, byte_string_view code)
    {
        evmc::Result result{
            evmc_result{.status_code = EVMC_SUCCESS, .gas_left = msg.gas}};
        if (code.empty()) {
            return result;
        }

        evmone::VM vm{};
#ifdef EVMONE_TRACING
        std::ostringstream instruction_trace_string_stream;
        vm.add_tracer(
            evmone::create_instruction_tracer(instruction_trace_string_stream));
#endif

        auto execution_state = std::make_unique<evmone::ExecutionState>(
            msg,
            Traits::rev,
            host->get_interface(),
            host->to_context(),
            code,
            byte_string_view{});
        evmone::baseline::CodeAnalysis code_analysis{
            evmone::baseline::analyze(Traits::rev, code)};
        result = evmc::Result{evmone::baseline::execute(
            vm, msg.gas, *execution_state, code_analysis)};

#ifdef EVMONE_TRACING
        LOG_TRACE_L1("{}", instruction_trace_string_stream.str());
#endif
        return result;
    }
};

MONAD_NAMESPACE_END
