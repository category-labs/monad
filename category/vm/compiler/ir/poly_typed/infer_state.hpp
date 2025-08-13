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

#include <category/vm/compiler/ir/poly_typed/subst_map.hpp>

#include <optional>
#include <unordered_map>

namespace monad::vm::compiler::poly_typed
{
    struct InferState
    {
        std::unordered_map<byte_offset, block_id> const &jumpdests;
        std::vector<local_stacks::Block> &&pre_blocks;
        VarName next_cont_var_name;
        VarName next_kind_var_name;
        VarName next_literal_var_name;
        SubstMap subst_map;
        std::unordered_map<block_id, ContKind> block_types;
        std::unordered_map<block_id, Terminator> block_terminators;

        InferState(
            std::unordered_map<byte_offset, block_id> const &jumpdests,
            std::vector<local_stacks::Block> &&pre_blocks);

        void reset();

        std::optional<block_id> get_jumpdest(Value const &) const;

        std::vector<block_id> static_successors(block_id b) const;

        VarName fresh_cont_var()
        {
            return next_cont_var_name++;
        }

        VarName fresh_kind_var()
        {
            return next_kind_var_name++;
        }

        VarName fresh_literal_var()
        {
            return next_literal_var_name++;
        }

        ContKind get_type(block_id);
    };
}
