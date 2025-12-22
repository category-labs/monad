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

#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/ir/x86/emitter.hpp>

using namespace monad::vm::compiler::native;

namespace monad::vm::compiler::bound_inference
{
    // Compute bounds on the result of an instruction, if possible.
    // It may also not compute the tightest possible bound for instructions that
    // are constant folded, i.e. composed only of literals.
    std::uint32_t compute_result_bound(Emitter &emit, Instruction const &instr);
}
