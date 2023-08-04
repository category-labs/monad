#pragma once

#include <evmone/instructions_traits.hpp>
#include <evmone/tracing.hpp>
#include <sstream>
#include <stack>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace
{
    std::string get_name(uint8_t opcode)
    {
        // TODO: Create constexpr tables of names (maybe even per revision).
        const auto name = evmone::instr::traits[opcode].name;
        return (name != nullptr) ? name : "0x" + evmc::hex(opcode);
    }
}

class InstructionTracer : public evmone::Tracer
{
    struct Context
    {
        const uint8_t *const code; ///< Reference to the code being executed.
        const int64_t start_gas;

        Context(const uint8_t *c, int64_t g) noexcept
            : code{c}
            , start_gas{g}
        {
        }
    };

    std::stack<Context> m_contexts;
    static std::ostringstream out; ///< Output stream.

    void output_stack(const intx::uint256 *stack_top, int stack_height)
    {
        InstructionTracer::out << R"(,"stack":[)";
        const auto stack_end = stack_top + 1;
        const auto stack_begin = stack_end - stack_height;
        for (auto it = stack_begin; it != stack_end; ++it) {
            if (it != stack_begin)
                InstructionTracer::out << ',';
            InstructionTracer::out << R"("0x)" << to_string(*it, 16) << '"';
        }
        InstructionTracer::out << ']';
    }

    void on_execution_start(
        evmc_revision rev, const evmc_message &msg,
        monad::byte_string_view code) noexcept override
    {
        m_contexts.emplace(code.data(), msg.gas);

        InstructionTracer::out << "{";
        InstructionTracer::out << R"("depth":)" << msg.depth;
        InstructionTracer::out << R"(,"rev":")" << rev << '"';
        InstructionTracer::out
            << R"(,"static":)"
            << (((msg.flags & EVMC_STATIC) != 0) ? "true" : "false");
        InstructionTracer::out << "}\n";
    }

    void on_instruction_start(
        uint32_t pc, const intx::uint256 *stack_top, int stack_height,
        int64_t gas, const evmone::ExecutionState &state) noexcept override
    {
        const auto &ctx = m_contexts.top();

        const auto opcode = ctx.code[pc];
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

        InstructionTracer::out << "}\n";
    }

    void on_execution_end(const evmc_result &result) noexcept override
    {
        const auto &ctx = m_contexts.top();

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

std::ostringstream InstructionTracer::out;

MONAD_EXECUTION_NAMESPACE_END
