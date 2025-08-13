// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

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
