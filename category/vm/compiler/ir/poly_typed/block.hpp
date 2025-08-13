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

#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>

namespace monad::vm::compiler::poly_typed
{
    using ValueIs = local_stacks::ValueIs;
    using Value = local_stacks::Value;

    struct FallThrough
    {
        ContKind fallthrough_kind;
        block_id fallthrough_dest;
    };

    struct JumpI
    {
        ContKind fallthrough_kind;
        ContKind jump_kind;
        block_id fallthrough_dest;
    };

    struct Jump
    {
        ContKind jump_kind;
    };

    struct Return
    {
    };

    struct Stop
    {
    };

    struct Revert
    {
    };

    struct SelfDestruct
    {
    };

    struct InvalidInstruction
    {
    };

    using Terminator = std::variant<
        FallThrough, JumpI, Jump, Return, Stop, Revert, SelfDestruct,
        InvalidInstruction>;

    struct Block
    {
        byte_offset offset;
        size_t min_params;
        std::vector<Value> output;
        std::vector<Instruction> instrs;
        ContKind kind;
        Terminator terminator;
    };
}
