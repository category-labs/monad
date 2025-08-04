#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/types.hpp>

#include <category/vm/core/assert.h>
#include <category/vm/runtime/uint256.hpp>

#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <limits>
#include <utility>
#include <vector>

namespace
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::compiler::local_stacks;
    using namespace monad::vm::runtime;

    void
    eval_instruction_fallback(Instruction const &tok, std::deque<Value> &stack)
    {
        for (std::size_t i = 0; i < tok.stack_args(); ++i) {
            stack.pop_front();
        }

        if (tok.increases_stack()) {
            stack.emplace_front(ValueIs::COMPUTED, 0);
        }
    }

    void eval_ternary_instruction(
        Instruction const &tok, std::deque<Value> &stack,
        std::function<
            uint256_t(uint256_t const &, uint256_t const &, uint256_t const &)>
            f)
    {
        Value const &x = stack[0];
        Value const &y = stack[1];
        Value &z = stack[2];
        if (x.is == ValueIs::LITERAL && y.is == ValueIs::LITERAL &&
            z.is == ValueIs::LITERAL) {
            z.literal = f(x.literal, y.literal, z.literal);
            stack.pop_front();
            stack.pop_front();
        }
        else {
            eval_instruction_fallback(tok, stack);
        }
    }

    void eval_binary_instruction(
        Instruction const &tok, std::deque<Value> &stack,
        std::function<uint256_t(uint256_t const &, uint256_t const &)> f)
    {
        Value const &x = stack[0];
        Value &y = stack[1];
        if (x.is == ValueIs::LITERAL && y.is == ValueIs::LITERAL) {
            y.literal = f(x.literal, y.literal);
            stack.pop_front();
        }
        else {
            eval_instruction_fallback(tok, stack);
        }
    }

    void eval_unary_instruction(
        Instruction const &tok, std::deque<Value> &stack,
        std::function<uint256_t(uint256_t const &)> f)
    {
        Value &x = stack[0];
        if (x.is == ValueIs::LITERAL) {
            x.literal = f(x.literal);
        }
        else {
            eval_instruction_fallback(tok, stack);
        }
    }

    void eval_instruction(
        Instruction const &tok, std::deque<Value> &stack, uint64_t codesize)
    {
        using enum OpCode;

        switch (tok.opcode()) {
        case Add:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return x + y; });
            break;
        case Mul:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return x * y; });
            break;
        case Sub:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return x - y; });
            break;
        case Div:
            eval_binary_instruction(tok, stack, [](auto &x, auto &y) {
                if (y == uint256_t{0}) {
                    return uint256_t{0};
                }
                return x / y;
            });
            break;
        case SDiv:
            eval_binary_instruction(tok, stack, [](auto &x, auto &y) {
                if (y == uint256_t{0}) {
                    return uint256_t{0};
                }
                return sdivrem(x, y).quot;
            });
            break;
        case Mod:
            eval_binary_instruction(tok, stack, [](auto &x, auto &y) {
                if (y == uint256_t{0}) {
                    return uint256_t{0};
                }
                return x % y;
            });
            break;
        case SMod:
            eval_binary_instruction(tok, stack, [](auto &x, auto &y) {
                if (y == uint256_t{0}) {
                    return uint256_t{0};
                }
                return sdivrem(x, y).rem;
            });
            break;
        case AddMod:
            eval_ternary_instruction(tok, stack, [](auto &x, auto &y, auto &m) {
                if (m == uint256_t{0}) {
                    return uint256_t{0};
                }
                return addmod(x, y, m);
            });
            break;
        case MulMod:
            eval_ternary_instruction(tok, stack, [](auto &x, auto &y, auto &m) {
                if (m == uint256_t{0}) {
                    return uint256_t{0};
                }
                return mulmod(x, y, m);
            });
            break;
        case Exp:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return exp(x, y); });
            break;
        case SignExtend:
            eval_binary_instruction(tok, stack, signextend);
            break;
        case Lt:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return uint256_t{x < y}; });
            break;
        case Gt:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return uint256_t{x > y}; });
            break;
        case SLt:
            eval_binary_instruction(tok, stack, [](auto &x, auto &y) {
                return uint256_t{slt(x, y)};
            });
            break;
        case SGt:
            eval_binary_instruction(tok, stack, [](auto &x, auto &y) {
                return uint256_t{slt(y, x)};
            });
            break;
        case Eq:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return uint256_t{x == y}; });
            break;
        case IsZero:
            eval_unary_instruction(tok, stack, [](auto &x) {
                return uint256_t{x == uint256_t{0}};
            });
            break;
        case And:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return x & y; });
            break;
        case Or:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return x | y; });
            break;
        case XOr:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return x ^ y; });
            break;
        case Not:
            eval_unary_instruction(tok, stack, [](auto &x) { return ~x; });
            break;
        case Byte:
            eval_binary_instruction(tok, stack, byte);
            break;
        case Shl:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return y << x; });
            break;
        case Shr:
            eval_binary_instruction(
                tok, stack, [](auto &x, auto &y) { return y >> x; });
            break;
        case Sar:
            eval_binary_instruction(tok, stack, sar);
            break;
        case CodeSize:
            stack.emplace_front(ValueIs::LITERAL, uint256_t{codesize});
            break;
        case Pop:
            stack.pop_front();
            break;
        case Pc:
            stack.emplace_front(ValueIs::LITERAL, tok.pc());
            break;
        case Push:
            stack.emplace_front(ValueIs::LITERAL, tok.immediate_value());
            break;
        case Dup:
            stack.push_front(stack[tok.index() - 1]);
            break;
        case Swap:
            std::swap(stack[0], stack[tok.index()]);
            break;
        default:
            eval_instruction_fallback(tok, stack);
        }
    }
}

namespace monad::vm::compiler::local_stacks
{
    LocalStacksIR::LocalStacksIR(basic_blocks::BasicBlocksIR ir)
        : jumpdests(std::move(ir.jump_dests()))
        , codesize(ir.codesize)
    {
        for (auto &blk : ir.blocks()) {
            blocks.push_back(convert_block(std::move(blk), codesize));
        }
    }

    Value::Value(ValueIs is, uint256_t data)
        : is(is)
    {
        switch (is) {
        case ValueIs::LITERAL:
            literal = data;
            break;
        case ValueIs::PARAM_ID:
            static_assert(sizeof(size_t) <= sizeof(uint64_t));
            MONAD_VM_ASSERT(
                data <= uint256_t{std::numeric_limits<size_t>::max()});
            param = data[0];
        default:
            // do nothing
            break;
        }
    };

    Block convert_block(basic_blocks::Block in, uint64_t codesize)
    {
        auto out = Block{
            .min_params = 0,
            .output = {},
            .instrs = std::move(in.instrs),
            .terminator = in.terminator,
            .fallthrough_dest = in.fallthrough_dest,
            .offset = in.offset,
        };

        std::deque<Value> stack;

        auto grow_stack_to_min_size = [&](size_t min_size) {
            while (stack.size() < min_size) {
                stack.emplace_back(ValueIs::PARAM_ID, out.min_params);
                out.min_params++;
            }
        };

        for (auto const &instr : out.instrs) {
            grow_stack_to_min_size(instr.stack_args());
            eval_instruction(instr, stack, codesize);
        }

        grow_stack_to_min_size(basic_blocks::terminator_inputs(out.terminator));

        out.output.insert(out.output.end(), stack.begin(), stack.end());
        return out;
    }

}
