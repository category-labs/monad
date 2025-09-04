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

#include <category/vm/compiler/ir/poly_typed.hpp>
#include <category/vm/compiler/ir/poly_typed/block.hpp>
#include <category/vm/interpreter/intercode.hpp>

namespace monad::vm::compiler::untyped
{

    struct Word
    {
    };

    struct Addr
    {
    };

    struct Invalid
    {
    };

    using JumpDest = std::variant<block_id, Word, Addr, Invalid>;

    struct FallThrough
    {
        std::vector<size_t> fallthrough_coerce_to_addr;
        block_id fallthrough_dest;
    };

    struct JumpI
    {
        std::vector<size_t> coerce_to_addr;
        JumpDest jump_dest;
        std::vector<size_t> fallthrough_coerce_to_addr;
        block_id fallthrough_dest;
    };

    struct Jump
    {
        std::vector<size_t> coerce_to_addr;
        JumpDest jump_dest;
    };

    struct DeadCode
    {
    };

    using Terminator = std::variant<
        FallThrough, JumpI, Jump, poly_typed::Return, poly_typed::Stop,
        poly_typed::Revert, poly_typed::SelfDestruct,
        poly_typed::InvalidInstruction, DeadCode>;

    struct Block
    {
        byte_offset offset;
        size_t min_params;
        std::vector<Instruction> instrs;
        Terminator terminator;
    };

    struct UntypedIR
    {
        explicit UntypedIR(poly_typed::PolyTypedIR &&ir);

        interpreter::code_size_t codesize;
        std::unordered_map<byte_offset, block_id> jumpdests;
        std::variant<std::vector<Block>, std::vector<local_stacks::Block>>
            blocks;
    };

    std::variant<std::vector<Block>, std::vector<local_stacks::Block>>
    build_untyped(
        std::unordered_map<byte_offset, block_id> const &jumpdests,
        std::vector<poly_typed::Block> &&typed_blocks);

}

template <>
struct std::formatter<monad::vm::compiler::untyped::UntypedIR>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    std::format_context::iterator format(
        monad::vm::compiler::untyped::UntypedIR const &ir,
        std::format_context &ctx) const;
};

template <>
struct std::formatter<monad::vm::compiler::untyped::JumpDest>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::untyped::JumpDest const &jd,
        std::format_context &ctx) const
    {
        using monad::vm::Cases;
        using namespace monad::vm::compiler::untyped;

        std::visit<void>(
            Cases{
                [&](Word const &) { std::format_to(ctx.out(), "WORD"); },
                [&](Addr const &) { std::format_to(ctx.out(), "ADDR"); },
                [&](Invalid const &) { std::format_to(ctx.out(), "INVALID"); },
                [&](monad::vm::compiler::block_id id) {
                    std::format_to(ctx.out(), "BLOCK_{}", id);
                },
            },
            jd);

        return ctx.out();
    }
};
