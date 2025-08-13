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

#include <category/vm/compiler/ir/basic_blocks.hpp>

#include <functional>

namespace monad::vm::compiler::local_stacks
{
    enum class ValueIs
    {
        PARAM_ID,
        COMPUTED,
        LITERAL
    };

    struct Value
    {
        ValueIs is;

        union
        {
            uint256_t literal;
            std::size_t param;
        }; // unused if COMPUTED

        Value(ValueIs is, uint256_t data);
    };

    struct Block
    {
        std::size_t min_params;
        std::vector<Value> output;

        std::vector<Instruction> instrs;
        basic_blocks::Terminator terminator;
        block_id fallthrough_dest; // value for JumpI and JumpDest, otherwise
                                   // INVALID_BLOCK_ID
        byte_offset offset;
    };

    class LocalStacksIR
    {
    public:
        explicit LocalStacksIR(basic_blocks::BasicBlocksIR ir);

        std::unordered_map<byte_offset, block_id> jumpdests;
        std::vector<Block> blocks;
        uint64_t codesize;
    };

    Block convert_block(basic_blocks::Block block, uint64_t codesize);
}

template <>
struct std::formatter<monad::vm::compiler::local_stacks::Value>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::local_stacks::Value const &val,
        std::format_context &ctx) const
    {
        switch (val.is) {
        case monad::vm::compiler::local_stacks::ValueIs::PARAM_ID:
            return std::format_to(ctx.out(), "%p{}", val.param);
        case monad::vm::compiler::local_stacks::ValueIs::COMPUTED:
            return std::format_to(ctx.out(), "COMPUTED");
        default:
            return std::format_to(ctx.out(), "{}", val.literal);
        }
    }
};

template <>
struct std::formatter<monad::vm::compiler::local_stacks::Block>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::local_stacks::Block const &blk,
        std::format_context &ctx) const
    {

        std::format_to(ctx.out(), "    min_params: {}\n", blk.min_params);

        for (auto const &tok : blk.instrs) {
            std::format_to(ctx.out(), "      {}\n", tok);
        }

        std::format_to(ctx.out(), "    {}", blk.terminator);
        if (blk.fallthrough_dest != monad::vm::compiler::INVALID_BLOCK_ID) {
            std::format_to(ctx.out(), " {}", blk.fallthrough_dest);
        }
        std::format_to(ctx.out(), "\n    output: [");
        for (monad::vm::compiler::local_stacks::Value const &val : blk.output) {
            std::format_to(ctx.out(), " {}", val);
        }
        return std::format_to(ctx.out(), " ]\n");
    }
};

template <>
struct std::formatter<monad::vm::compiler::local_stacks::LocalStacksIR>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::local_stacks::LocalStacksIR const &ir,
        std::format_context &ctx) const
    {

        std::format_to(ctx.out(), "local_stacks:\n");
        int i = 0;
        for (auto const &blk : ir.blocks) {
            std::format_to(ctx.out(), "  block {} - 0x{}:\n", i, blk.offset);
            std::format_to(ctx.out(), "{}", blk);
            i++;
        }
        std::format_to(ctx.out(), "\n  jumpdests:\n");
        for (auto const &[k, v] : ir.jumpdests) {
            std::format_to(ctx.out(), "    {}:{}\n", k, v);
        }
        return std::format_to(ctx.out(), "");
    }
};
