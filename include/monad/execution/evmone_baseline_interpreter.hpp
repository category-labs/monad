#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/concepts.hpp>

#include <monad/execution/config.hpp>
#include <monad/logging/monad_log.hpp>

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
    #include <sstream>
#endif

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, concepts::fork_traits<TState> TTraits>
struct EVMOneBaselineInterpreter
{
    template <class TEvmHost>
    static evmc::Result
    execute(TEvmHost *h, evmc_message const &m, byte_string_view code)
    {
        [[maybe_unused]] decltype(monad::log::logger_t::get_logger()) logger =
            monad::log::logger_t::get_logger(
                "evmone_baseline_interpreter_logger");
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

        evmone::ExecutionState es{
            m, TTraits::rev, h->get_interface(), h->to_context(), code, {}};
        evmone::baseline::CodeAnalysis ca{
            evmone::baseline::analyze(TTraits::rev, code)};
        result = evmc::Result{evmone::baseline::execute(v, m.gas, es, ca)};

#ifdef EVMONE_TRACING
        MONAD_LOG_DEBUG(logger, "{}", instruction_trace_string_stream.str());
#endif
        return result;
    }
};

MONAD_EXECUTION_NAMESPACE_END
