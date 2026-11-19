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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/interpreter/handler_policy.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/stack_top.hpp>
#include <category/vm/runtime/types.hpp>

#include <array>
#include <cstdint>

namespace monad::vm::interpreter
{
    // Use void const * to pass either a slot base or a pointer table without
    // making InstrEval recursive.
    using InstrEval = void MONAD_VM_POINTER_CALL (*)(
        runtime::Context &, Intercode const &, uint256_t const *, StackTop,
        int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    using InstrTable = std::array<InstrEval, 256>;
}
