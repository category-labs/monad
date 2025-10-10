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

#pragma once

#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <test/vm/untyped_ir_interpreter/intercode_untyped_ir.hpp>

#include <array>
#include <cstdint>

namespace monad::vm::interpreter
{
    using InstrEvalUntypedIR = void MONAD_VM_INSTRUCTION_CALL (*)(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    using InstrTableUntypedIR = std::array<InstrEvalUntypedIR, 256>;
}
