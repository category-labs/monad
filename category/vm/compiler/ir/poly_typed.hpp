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

#include <category/vm/compiler/ir/poly_typed/block.hpp>

namespace monad::vm::compiler::poly_typed
{
    struct PolyTypedIR
    {
        explicit PolyTypedIR(local_stacks::LocalStacksIR &&ir);

        void type_check_or_throw();
        bool type_check();

        uint64_t codesize;
        std::unordered_map<byte_offset, block_id> jumpdests;
        std::vector<Block> blocks;
    };
}

template <>
struct std::formatter<monad::vm::compiler::poly_typed::PolyTypedIR>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    std::format_context::iterator format(
        monad::vm::compiler::poly_typed::PolyTypedIR const &ir,
        std::format_context &ctx) const;
};
