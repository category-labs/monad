// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/instruction_table.hpp>

#include <magic_enum/magic_enum.hpp>

#include <monad/test/traits_test.hpp>

#include <gtest/gtest.h>

#include <cstddef>

using namespace monad::vm::compiler;
using namespace monad::vm::interpreter;

template <>
struct magic_enum::customize::enum_range<EvmOpCode>
{
    static constexpr int min = 0;
    static constexpr int max = 255;
};

namespace
{
    template <monad::Traits traits>
    consteval bool opcode_tables_agree()
    {
        for (std::size_t i = 0; i < 256; ++i) {
            auto const opcode = static_cast<EvmOpCode>(i);
            bool const unknown = is_unknown_opcode_info<traits>(opcode);
            auto const name = opcode == DIFFICULTY
                                  ? eip_4399_name<traits>()
                                  : magic_enum::enum_name(opcode);
            if (!unknown && opcode_table<traits>[i].name != name) {
                return false;
            }
            if (unknown != (instruction_table<traits>[i] == invalid)) {
                return false;
            }
        }
        return true;
    }
}

TYPED_TEST(TraitsTest, OpcodeTablesAgree)
{
    static_assert(opcode_tables_agree<typename TestFixture::Trait>());
}
