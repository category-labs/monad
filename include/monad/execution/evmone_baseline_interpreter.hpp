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

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, concepts::fork_traits<TState> TTraits>
struct EVMOneBaselineInterpreter
{
    template <class TEvmHost>
    static evmc_result
    execute(TState const &s, TEvmHost *h, evmc_message const &m)
    {
        auto const code =
            s.code_at(m.sender); // call needs to be plumbed through state...
        if (code.empty()) {
            return {.status_code = EVMC_SUCCESS, .gas_left = m.gas};
        }

        evmone::VM v{};
        evmone::ExecutionState es{
            m,
            TTraits::rev,
            *reinterpret_cast<evmc_host_interface *>(h),
            nullptr,
            code,
            {}};
        evmone::baseline::CodeAnalysis ca{
            evmone::baseline::analyze(TTraits::rev, code)};
        return evmone::baseline::execute(v, m.gas, es, ca);
    }
};

MONAD_EXECUTION_NAMESPACE_END
