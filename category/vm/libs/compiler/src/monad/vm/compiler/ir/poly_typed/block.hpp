#pragma once

#include <monad/vm/compiler/ir/local_stacks.hpp>
#include <monad/vm/compiler/ir/poly_typed/kind.hpp>

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
