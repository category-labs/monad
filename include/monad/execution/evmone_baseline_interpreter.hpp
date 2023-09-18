#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/concepts.hpp>

#include <monad/execution/config.hpp>

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

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, concepts::fork_traits<TState> TTraits>
struct EVMOneBaselineInterpreter
{
    template <class TEvmHost>
    static evmc::Result
    execute(TEvmHost *h, evmc_message const &m, byte_string_view code)
    {
        evmc::Result result{
            evmc_result{.status_code = EVMC_SUCCESS, .gas_left = m.gas}};
        if (code.empty()) {
            return result;
        }

        evmone::VM v{};
#ifdef EVMONE_TRACING
        std::ostringstream instruction_trace_string_stream;
        v.add_tracer(
            evmone::create_instruction_tracer(instruction_trace_string_stream));
#endif

        auto es = std::make_unique<evmone::ExecutionState>(
            m,
            TTraits::rev,
            h->get_interface(),
            h->to_context(),
            code,
            byte_string_view{});
        evmone::baseline::CodeAnalysis ca{
            evmone::baseline::analyze(TTraits::rev, code)};
        result = evmc::Result{evmone::baseline::execute(v, m.gas, *es, ca)};

#ifdef EVMONE_TRACING
        QUILL_LOG_DEBUG(
            quill::get_logger("evmone_baseline_interpreter_logger"),
            "{}",
            instruction_trace_string_stream.str());
#endif
        return result;
    }
};

MONAD_EXECUTION_NAMESPACE_END
