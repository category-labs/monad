#pragma once

#include <monad/vm/compiler/ir/poly_typed/block.hpp>

namespace monad::vm::compiler::poly_typed
{
    struct PolyTypedIR
    {
        explicit PolyTypedIR(local_stacks::LocalStacksIR const &&ir);

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
