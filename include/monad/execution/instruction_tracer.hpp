#pragma once
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>

#ifndef __clang__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored_attributes "clang::"
#endif
#include <evmone/execution_state.hpp>
#ifndef __clang__
    #pragma GCC diagnostic pop
#endif

#include <evmone/execution_state.hpp>
#include <evmone/instructions_traits.hpp>
#include <evmone/tracing.hpp>
#include <monad/execution/config.hpp>
#include <sstream>
#include <stack>

MONAD_EXECUTION_NAMESPACE_BEGIN

class InstructionTracer : public evmone::Tracer
{
    struct Context
    {
        uint8_t const *const code; ///< Reference to the code being executed.
        int64_t const start_gas;
        int32_t const depth;

        Context(uint8_t const *c, int64_t g, int32_t depth) noexcept
            : code{c}
            , start_gas{g}
            , depth{depth}
        {
        }
    };

    std::stack<Context> m_contexts;
    static std::ostringstream out; ///< Output stream.
    static std::optional<int64_t> previous_gas;

    void output_stack(intx::uint256 const *stack_top, int stack_height);

    void on_execution_start(
        [[maybe_unused]] evmc_revision rev, evmc_message const &msg,
        monad::byte_string_view code) noexcept override;

    void on_instruction_start(
        uint32_t pc, intx::uint256 const *stack_top, int stack_height,
        int64_t gas,
        [[maybe_unused]] evmone::ExecutionState const &state) noexcept override;

    void on_execution_end(evmc_result const &result) noexcept override;

public:
    explicit InstructionTracer() noexcept;

    static std::string get_trace()
    {
        auto res = InstructionTracer::out.str();
        InstructionTracer::out.str("");
        return res;
    }
};

MONAD_EXECUTION_NAMESPACE_END
