// #include <monad/execution/instruction_tracer.hpp>
#include <monad/execution/instruction_tracer.hpp>

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

std::ostringstream InstructionTracer::out;
std::optional<int64_t> InstructionTracer::previous_gas;

void InstructionTracer::output_stack(
    intx::uint256 const *stack_top, int stack_height)
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

void InstructionTracer::on_execution_start(
    [[maybe_unused]] evmc_revision rev, evmc_message const &msg,
    monad::byte_string_view code) noexcept
{
    m_contexts.emplace(code.data(), msg.gas, msg.depth);
}

void InstructionTracer::on_instruction_start(
    uint32_t pc, intx::uint256 const *stack_top, int stack_height, int64_t gas,
    [[maybe_unused]] evmone::ExecutionState const &state) noexcept
{
    auto const &ctx = m_contexts.top();

    auto const opcode = ctx.code[pc];
    InstructionTracer::out << "{";
    InstructionTracer::out << R"("pc":)" << std::dec << pc;
    InstructionTracer::out << R"(,"op":)" << std::dec << int{opcode};
    InstructionTracer::out << R"(,"gas":"0x)" << std::hex << gas << "\"";

    InstructionTracer::out
        << R"(,"gasCost":"0x)"
        << std::hex
        //        << (previous_gas.has_value()
        //                ? (previous_gas.value() - gas)
        //                : evmone::instr::gas_costs[state.rev][opcode])
        << evmone::instr::gas_costs[state.rev][opcode] << "\"";
    previous_gas = gas;

    // Full memory can be dumped as evmc::hex({state.memory.data(),
    // state.memory.size()}), but this should not be done by default. Adding
    // --tracing=+memory option would be nice.
    InstructionTracer::out << R"(,"memSize":)" << std::dec
                           << state.memory.size();
    output_stack(stack_top, stack_height);
    InstructionTracer::out << R"(,"depth":)" << std::dec
                           << (state.msg->depth + 1);
    InstructionTracer::out << R"(,"refund":)" << std::dec << (state.gas_refund);
    InstructionTracer::out << R"(,"opName":")" << get_name(opcode) << '"';

    InstructionTracer::out << "}\n";
}

void InstructionTracer::on_execution_end(evmc_result const &result) noexcept
{
    auto const &ctx = m_contexts.top();

    if (ctx.depth == 0) {
        InstructionTracer::out << "{";
        if (result.status_code != EVMC_SUCCESS) {
            InstructionTracer::out << R"("error":)";
            InstructionTracer::out << '"' << result.status_code << "\",";
        }
        InstructionTracer::out
            << R"("output":")"
            << evmc::hex({result.output_data, result.output_size}) << '"';
        InstructionTracer::out << R"(,"gasUsed":)" << std::hex << "\"0x"
                               << (ctx.start_gas - result.gas_left) << "\"";
        InstructionTracer::out << "}\n";
    }

    m_contexts.pop();
}

InstructionTracer::InstructionTracer() noexcept
{
    InstructionTracer::out
        << std::dec; // Set number formatting to dec, JSON does not
    // support other forms.
}

MONAD_EXECUTION_NAMESPACE_END
