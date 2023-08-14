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

namespace
{
    std::string get_name(uint8_t opcode)
    {
        // TODO: Create constexpr tables of names (maybe even per revision).
        auto const name = evmone::instr::traits[opcode].name;
        return (name != nullptr) ? name : "0x" + evmc::hex(opcode);
    }
}

class InstructionTracer : public evmone::Tracer
{
    struct Context
    {
        uint8_t const *const code; ///< Reference to the code being executed.
        int64_t const start_gas;

        Context(uint8_t const *c, int64_t g) noexcept
            : code{c}
            , start_gas{g}
        {
        }
    };

    std::stack<Context> m_contexts;
    static std::ostringstream out; ///< Output stream.

    void output_stack(intx::uint256 const *stack_top, int stack_height)
    {
        InstructionTracer::out << R"(,"stack":[)";
        auto const stack_end = stack_top + 1;
        auto const stack_begin = stack_end - stack_height;
        for (auto it = stack_begin; it != stack_end; ++it) {
            if (it != stack_begin)
                InstructionTracer::out << ',';
            InstructionTracer::out << R"("0x)" << to_string(*it, 16) << '"';
        }
        InstructionTracer::out << ']';
    }

    void on_execution_start(
        [[maybe_unused]] evmc_revision rev, evmc_message const &msg,
        monad::byte_string_view code) noexcept override
    {
        m_contexts.emplace(code.data(), msg.gas);
    }

    void on_instruction_start(
        uint32_t pc, intx::uint256 const *stack_top, int stack_height,
        int64_t gas,
        [[maybe_unused]] evmone::ExecutionState const &state) noexcept override
    {
        auto const &ctx = m_contexts.top();

        auto const opcode = ctx.code[pc];
        InstructionTracer::out << "{";
        InstructionTracer::out << R"("pc":)" << std::dec << pc;
        InstructionTracer::out << R"(,"op":)" << std::dec << int{opcode};
        InstructionTracer::out << R"(,"opName":")" << get_name(opcode) << '"';
        InstructionTracer::out << R"(,"gas":"0x)" << std::hex << gas << "\"";
        output_stack(stack_top, stack_height);

        // Full memory can be dumped as evmc::hex({state.memory.data(),
        // state.memory.size()}), but this should not be done by default. Adding
        // --tracing=+memory option would be nice.
        InstructionTracer::out << R"(,"memorySize":)" << std::dec
                               << state.memory.size();
        InstructionTracer::out << R"("depth":)" << std::dec
                               << (state.msg->depth + 1);

        InstructionTracer::out << "}\n";
    }

    void on_execution_end(evmc_result const &result) noexcept override
    {
        auto const &ctx = m_contexts.top();

        InstructionTracer::out << "{";
        InstructionTracer::out << R"("error":)";
        if (result.status_code == EVMC_SUCCESS)
            InstructionTracer::out << "null";
        else
            InstructionTracer::out << '"' << result.status_code << '"';
        InstructionTracer::out << R"(,"gas":)" << std::hex << "\"0x"
                               << result.gas_left << "\"";
        InstructionTracer::out << R"(,"gasUsed":)" << std::hex << "\"0x"
                               << (ctx.start_gas - result.gas_left) << "\"";
        InstructionTracer::out
            << R"(,"output":")"
            << evmc::hex({result.output_data, result.output_size}) << '"';
        InstructionTracer::out << "}\n";

        m_contexts.pop();
    }

public:
    explicit InstructionTracer() noexcept
    {
        InstructionTracer::out
            << std::dec; // Set number formatting to dec, JSON does not
                         // support other forms.
    }

    static std::string get_trace()
    {
        auto res = InstructionTracer::out.str();
        InstructionTracer::out.str("");
        return res;
    }
};

MONAD_EXECUTION_NAMESPACE_END
