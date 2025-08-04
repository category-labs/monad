#include <category/vm/fuzzing/generator/instruction_data.hpp>

#include <cstdint>
#include <unordered_map>
#include <vector>

namespace monad::vm::fuzzing
{
    std::vector<std::uint8_t> const &
    memory_operands(std::uint8_t const opcode) noexcept
    {
        static auto const empty = std::vector<std::uint8_t>{};
        static auto const data =
            std::unordered_map<std::uint8_t, std::vector<std::uint8_t>>{
                {SHA3, {0, 1}},
                {CALLDATACOPY, {0, 2}},
                {CODECOPY, {0, 2}},
                {EXTCODECOPY, {1, 3}},
                {RETURNDATACOPY, {0, 2}},
                {MLOAD, {0}},
                {MSTORE, {0}},
                {MSTORE8, {0}},
                {MCOPY, {0, 1, 2}},
                {LOG0, {0, 1}},
                {LOG1, {0, 1}},
                {LOG2, {0, 1}},
                {LOG3, {0, 1}},
                {LOG4, {0, 1}},
                {CREATE, {1, 2}},
                {CALL, {3, 4, 5, 6}},
                {CALLCODE, {3, 4, 5, 6}},
                {RETURN, {0, 1}},
                {DELEGATECALL, {2, 3, 4, 5}},
                {CREATE2, {1, 2}},
                {STATICCALL, {2, 3, 4, 5}},
                {REVERT, {0, 1}},
            };

        if (data.contains(opcode)) {
            return data.at(opcode);
        }

        return empty;
    }

    bool uses_memory(std::uint8_t const opcode) noexcept
    {
        return !memory_operands(opcode).empty();
    }
}
