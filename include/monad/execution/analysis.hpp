#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/execution/config.hpp>

#ifndef __clang__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored_attributes "clang::"
#endif
#include <evmone/instructions.hpp>
#include <evmone/instructions_opcodes.hpp>
#include <evmone/instructions_traits.hpp>
#ifndef __clang__
    #pragma GCC diagnostic pop
#endif

#include <format>
#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

struct Instruction
{
    Instruction(evmone::Opcode opcode)
        : opcode{opcode}
        , data{}
    {
    }

    Instruction(evmone::Opcode opcode, monad::bytes32_t data)
        : opcode{opcode}
        , data{data}
    {
    }

    bool operator==(Instruction const &rhs) const
    {
        return opcode == rhs.opcode && data == rhs.data;
    }
    bool operator!=(Instruction const &rhs) const { return !(rhs == *this); }

    evmone::Opcode const opcode;
    // TODO: for better performance, we can store immediate opcode data
    // separately since only push opcodes use it
    monad::bytes32_t const data;
};

/**
 * @param code
 * @return a tokenized list of opcodes.
 * @throws std::invalid argument if
 * - code contains an invalid opcode
 * - parsing an opcode would result in reading out of bounds code
 * - the `immediate_size` member of an instruction would lead to overrunning
 *   a bytes32_t
 */
auto tokenize_code(monad::byte_string_view code)
{
    std::vector<Instruction> tokens;
    tokens.reserve(code.size());

    // only used for error reporting
    auto const *code_start = code.data();

    while (!code.empty()) {
        auto const opcode = *code.begin();
        auto const offset = code.data() - code_start;
        auto const instruction = ::evmone::instr::traits[opcode];
        auto const instruction_name =
            (instruction.name == nullptr) ? "null" : instruction.name;
        auto const immediate_size = instruction.immediate_size;

        if (MONAD_UNLIKELY(instruction.name == nullptr)) {
            throw std::invalid_argument{
                std::format("invalid opcode at code offset {}", offset)};
        }

        if (MONAD_UNLIKELY(std::cmp_less(code.size(), immediate_size + 1))) {
            throw std::invalid_argument{std::format(
                "parsing opcode {} at code offset {} would read past code view",
                instruction_name,
                offset)};
        }

        if (MONAD_UNLIKELY(immediate_size > sizeof(monad::bytes32_t))) {
            throw std::invalid_argument{std::format(
                "parsing immediate size {} operand for opcode {} at code "
                "offset {} would overflow monad::bytes32_t",
                immediate_size,
                instruction_name,
                offset)};
        }

        // consume opcode
        code.remove_prefix(1);

        monad::bytes32_t data{0};

        // on a big-endian arch, std::copy_n would suffice
        static_assert(std::endian::native == std::endian::little);
        std::copy_backward(
            code.data(),
            code.data() + immediate_size,
            data.bytes + sizeof(data));

        tokens.emplace_back(evmone::Opcode{opcode}, data);

        // consume immediate, if any
        code.remove_prefix(immediate_size);
    }

    return tokens;
}

MONAD_EXECUTION_NAMESPACE_END
