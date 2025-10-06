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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/call_runtime.hpp>
#include <category/vm/interpreter/debug.hpp>
#include <category/vm/interpreter/instructions_fwd.hpp>
#include <category/vm/interpreter/push.hpp>
#include <category/vm/interpreter/stack.hpp>
#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/runtime.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>
#include <category/vm/utils/debug.hpp>

#include <evmc/evmc.h>

#include <array>
#include <cstdint>
#include <memory>

#if defined(__has_attribute)
    #if __has_attribute(musttail)
        #define MONAD_VM_MUST_TAIL __attribute__((musttail))
    #else
        #error "No compiler support for __attribute__((musttail))"
    #endif
#else
    #error "No compiler support for __has_attribute"
#endif

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;
    using enum compiler::EvmOpCode;

    template <Traits traits>
    consteval InstrTable make_instruction_table()
    {
        constexpr auto since = [](evmc_revision first, InstrEval impl) {
            return (traits::evm_rev() >= first) ? impl
                                                : terminator_inline<invalid>;
        };

        return {
            terminator_inline<stop>, // 0x00
            wrap<traits, add, ADD>, // 0x01
            wrap<traits, mul, MUL>, // 0x02
            wrap<traits, sub, SUB>, // 0x03
            wrap<traits, udiv<traits>, DIV>, // 0x04,
            wrap<traits, sdiv<traits>, SDIV>, // 0x05,
            wrap<traits, umod<traits>, MOD>, // 0x06,
            wrap<traits, smod<traits>, SMOD>, // 0x07,
            wrap<traits, addmod<traits>, ADDMOD>, // 0x08,
            wrap<traits, mulmod<traits>, MULMOD>, // 0x09,
            wrap<traits, exp<traits>, EXP>, // 0x0A,
            wrap<traits, signextend, SIGNEXTEND>, // 0x0B,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            wrap<traits, lt, LT>, // 0x10,
            wrap<traits, gt, GT>, // 0x11,
            wrap<traits, slt, SLT>, // 0x12,
            wrap<traits, sgt, SGT>, // 0x13,
            wrap<traits, eq, EQ>, // 0x14,
            wrap<traits, iszero, ISZERO>, // 0x15,
            wrap<traits, and_, AND>, // 0x16,
            wrap<traits, or_, OR>, // 0x17,
            wrap<traits, xor_, XOR>, // 0x18,
            wrap<traits, not_, NOT>, // 0x19,
            wrap<traits, byte, BYTE>, // 0x1A,
            since(EVMC_CONSTANTINOPLE, wrap<traits, shl, SHL>), // 0x1B,
            since(EVMC_CONSTANTINOPLE, wrap<traits, shr, SHR>), // 0x1C,
            since(EVMC_CONSTANTINOPLE, wrap<traits, sar, SAR>), // 0x1D,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            wrap<traits, sha3, SHA3>, // 0x20,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>,
            //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            wrap<traits, address, ADDRESS>, // 0x30,
            wrap<traits, balance<traits>, BALANCE>, // 0x31,
            wrap<traits, origin, ORIGIN>, // 0x32,
            wrap<traits, caller, CALLER>, // 0x33,
            wrap<traits, callvalue, CALLVALUE>, // 0x34,
            wrap<traits, calldataload, CALLDATALOAD>, // 0x35,
            wrap<traits, calldatasize, CALLDATASIZE>, // 0x36,
            wrap<traits, calldatacopy, CALLDATACOPY>, // 0x37,
            wrap<traits, codesize, CODESIZE>, // 0x38,
            wrap<traits, codecopy, CODECOPY>, // 0x39,
            wrap<traits, gasprice, GASPRICE>, // 0x3A,
            wrap<traits, extcodesize<traits>, EXTCODESIZE>, // 0x3B,
            wrap<traits, extcodecopy<traits>, EXTCODECOPY>, // 0x3C,
            since(
                EVMC_BYZANTIUM,
                wrap<traits, returndatasize, RETURNDATASIZE>), // 0x3D,
            since(
                EVMC_BYZANTIUM,
                wrap<traits, returndatacopy, RETURNDATACOPY>), // 0x3E,
            since(
                EVMC_CONSTANTINOPLE,
                wrap<traits, extcodehash<traits>, EXTCODEHASH>), // 0x3F,

            wrap<traits, blockhash, BLOCKHASH>, // 0x40,
            wrap<traits, coinbase, COINBASE>, // 0x41,
            wrap<traits, timestamp, TIMESTAMP>, // 0x42,
            wrap<traits, number, NUMBER>, // 0x43,
            wrap<traits, prevrandao, DIFFICULTY>, // 0x44,
            wrap<traits, gaslimit, GASLIMIT>, // 0x45,
            since(EVMC_ISTANBUL, wrap<traits, chainid, CHAINID>), // 0x46,
            since(
                EVMC_ISTANBUL, wrap<traits, selfbalance, SELFBALANCE>), // 0x47,
            since(EVMC_LONDON, wrap<traits, basefee, BASEFEE>), // 0x48,
            since(EVMC_CANCUN, wrap<traits, blobhash, BLOBHASH>), // 0x49,
            since(EVMC_CANCUN, wrap<traits, blobbasefee, BLOBBASEFEE>), // 0x4A,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            wrap<traits, pop, POP>, // 0x50,
            wrap<traits, mload, MLOAD>, // 0x51,
            wrap<traits, mstore, MSTORE>, // 0x52,
            wrap<traits, mstore8, MSTORE8>, // 0x53,
            wrap<traits, sload<traits>, SLOAD>, // 0x54,
            wrap<traits, sstore<traits>, SSTORE>, // 0x55,
            jump<traits>, // 0x56,
            jumpi<traits>, // 0x57,
            wrap<traits, pc, PC>, // 0x58,
            wrap<traits, msize, MSIZE>, // 0x59,
            wrap<traits, gas, GAS>, // 0x5A,
            wrap<traits, jumpdest, JUMPDEST>, // 0x5B,
            since(EVMC_CANCUN, wrap<traits, tload, TLOAD>), // 0x5C,
            since(EVMC_CANCUN, wrap<traits, tstore, TSTORE>), // 0x5D,
            since(EVMC_CANCUN, wrap<traits, mcopy, MCOPY>), // 0x5E,
            since(EVMC_SHANGHAI, wrap<traits, push<0>, PUSH0>), // 0x5F,

            wrap<traits, push<1>, PUSH1>, // 0x60,
            wrap<traits, push<2>, PUSH2>, // 0x61,
            wrap<traits, push<3>, PUSH3>, // 0x62,
            wrap<traits, push<4>, PUSH4>, // 0x63,
            wrap<traits, push<5>, PUSH5>, // 0x64,
            wrap<traits, push<6>, PUSH6>, // 0x65,
            wrap<traits, push<7>, PUSH7>, // 0x66,
            wrap<traits, push<8>, PUSH8>, // 0x67,
            wrap<traits, push<9>, PUSH9>, // 0x68,
            wrap<traits, push<10>, PUSH10>, // 0x69,
            wrap<traits, push<11>, PUSH11>, // 0x6A,
            wrap<traits, push<12>, PUSH12>, // 0x6B,
            wrap<traits, push<13>, PUSH13>, // 0x6C,
            wrap<traits, push<14>, PUSH14>, // 0x6D,
            wrap<traits, push<15>, PUSH15>, // 0x6E,
            wrap<traits, push<16>, PUSH16>, // 0x6F,

            wrap<traits, push<17>, PUSH17>, // 0x70,
            wrap<traits, push<18>, PUSH18>, // 0x71,
            wrap<traits, push<19>, PUSH19>, // 0x72,
            wrap<traits, push<20>, PUSH20>, // 0x73,
            wrap<traits, push<21>, PUSH21>, // 0x74,
            wrap<traits, push<22>, PUSH22>, // 0x75,
            wrap<traits, push<23>, PUSH23>, // 0x76,
            wrap<traits, push<24>, PUSH24>, // 0x77,
            wrap<traits, push<25>, PUSH25>, // 0x78,
            wrap<traits, push<26>, PUSH26>, // 0x79,
            wrap<traits, push<27>, PUSH27>, // 0x7A,
            wrap<traits, push<28>, PUSH28>, // 0x7B,
            wrap<traits, push<29>, PUSH29>, // 0x7C,
            wrap<traits, push<30>, PUSH30>, // 0x7D,
            wrap<traits, push<31>, PUSH31>, // 0x7E,
            wrap<traits, push<32>, PUSH32>, // 0x7F,

            wrap<traits, dup<1>, DUP1>, // 0x80,
            wrap<traits, dup<2>, DUP2>, // 0x81,
            wrap<traits, dup<3>, DUP3>, // 0x82,
            wrap<traits, dup<4>, DUP4>, // 0x83,
            wrap<traits, dup<5>, DUP5>, // 0x84,
            wrap<traits, dup<6>, DUP6>, // 0x85,
            wrap<traits, dup<7>, DUP7>, // 0x86,
            wrap<traits, dup<8>, DUP8>, // 0x87,
            wrap<traits, dup<9>, DUP9>, // 0x88,
            wrap<traits, dup<10>, DUP10>, // 0x89,
            wrap<traits, dup<11>, DUP11>, // 0x8A,
            wrap<traits, dup<12>, DUP12>, // 0x8B,
            wrap<traits, dup<13>, DUP13>, // 0x8C,
            wrap<traits, dup<14>, DUP14>, // 0x8D,
            wrap<traits, dup<15>, DUP15>, // 0x8E,
            wrap<traits, dup<16>, DUP16>, // 0x8F,

            wrap<traits, swap<1>, SWAP1>, // 0x90,
            wrap<traits, swap<2>, SWAP2>, // 0x91,
            wrap<traits, swap<3>, SWAP3>, // 0x92,
            wrap<traits, swap<4>, SWAP4>, // 0x93,
            wrap<traits, swap<5>, SWAP5>, // 0x94,
            wrap<traits, swap<6>, SWAP6>, // 0x95,
            wrap<traits, swap<7>, SWAP7>, // 0x96,
            wrap<traits, swap<8>, SWAP8>, // 0x97,
            wrap<traits, swap<9>, SWAP9>, // 0x98,
            wrap<traits, swap<10>, SWAP10>, // 0x99,
            wrap<traits, swap<11>, SWAP11>, // 0x9A,
            wrap<traits, swap<12>, SWAP12>, // 0x9B,
            wrap<traits, swap<13>, SWAP13>, // 0x9C,
            wrap<traits, swap<14>, SWAP14>, // 0x9D,
            wrap<traits, swap<15>, SWAP15>, // 0x9E,
            wrap<traits, swap<16>, SWAP16>, // 0x9F,

            wrap<traits, log<0>, LOG0>, // 0xA0,
            wrap<traits, log<1>, LOG1>, // 0xA1,
            wrap<traits, log<2>, LOG2>, // 0xA2,
            wrap<traits, log<3>, LOG3>, // 0xA3,
            wrap<traits, log<4>, LOG4>, // 0xA4,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //

            wrap<traits, create<traits>, CREATE>, // 0xF0,
            wrap<traits, call<traits>, CALL>, // 0xF1,
            wrap<traits, callcode<traits>, CALLCODE>, // 0xF2,
            terminator<traits, return_<traits>>, // 0xF3,
            since(
                EVMC_HOMESTEAD,
                wrap<traits, delegatecall<traits>, DELEGATECALL>), // 0xF4,
            since(
                EVMC_CONSTANTINOPLE,
                wrap<traits, create2<traits>, CREATE2>), // 0xF5,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            since(
                EVMC_BYZANTIUM,
                wrap<traits, staticcall<traits>, STATICCALL>), // 0xFA,
            terminator_inline<invalid>, //
            terminator_inline<invalid>, //
            since(EVMC_BYZANTIUM, terminator<traits, revert<traits>>), // 0xFD,
            terminator_inline<invalid>, // 0xFE,
            terminator<traits, selfdestruct<traits>>, // 0xFF,
        };
    }

    template <Traits traits>
    constexpr InstrTable instruction_table = make_instruction_table<traits>();

#ifdef MONAD_COMPILER_TESTING
    [[gnu::always_inline]]
    inline void fuzz_tstore_stack(
        runtime::Context const &ctx, runtime::uint256_t const *stack_bottom,
        runtime::uint256_t const *stack_top, std::uint64_t base_offset)
    {
        if (!utils::is_fuzzing_monad_vm) {
            return;
        }
        monad::vm::runtime::debug_tstore_stack(
            &ctx,
            stack_top + 1,
            static_cast<uint64_t>(stack_top - stack_bottom),
            0,
            base_offset);
    }
#else
    [[gnu::always_inline]] inline void fuzz_tstore_stack(
        runtime::Context const &, runtime::uint256_t const *,
        runtime::uint256_t const *, std::uint64_t)
    {
        // nop
    }
#endif
    template <Traits traits, InstrEvalInline eval, compiler::EvmOpCode OP>
    MONAD_VM_INSTRUCTION_CALL void wrap(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        if constexpr (debug_enabled) {
            trace(analysis, gas_remaining, instr_ptr);
        }
        if constexpr (OP == JUMPDEST) {
            fuzz_tstore_stack(
                ctx,
                stack_bottom,
                stack_top,
                static_cast<uint64_t>(instr_ptr - analysis.code()));
        }

        check_requirements<OP, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);

        eval(ctx, analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);

        static constexpr auto delta =
            compiler::opcode_table<traits>[OP].stack_increase -
            compiler::opcode_table<traits>[OP].min_stack;

        ++instr_ptr;

        MONAD_VM_MUST_TAIL return instruction_table<traits>[*instr_ptr](
            ctx,
            analysis,
            stack_bottom,
            stack_top + delta,
            gas_remaining,
            instr_ptr);
    }

    template <InstrEvalInline eval>
    MONAD_VM_INSTRUCTION_CALL inline void terminator_inline(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        eval(ctx, analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);
    }

    template <Traits traits, InstrEvalInline eval>
    MONAD_VM_INSTRUCTION_CALL void terminator(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        eval(ctx, analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);
    }

    // Arithmetic
    [[gnu::always_inline]] inline void
    add(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a + b;
    }

    [[gnu::always_inline]] inline void
    mul(runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(monad_vm_runtime_mul, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void
    sub(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a - b;
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void udiv(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::udiv, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void sdiv(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::sdiv, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void umod(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::umod, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void smod(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::smod, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void addmod(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::addmod, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void mulmod(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::mulmod, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void
    exp(runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::exp<traits>, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void signextend(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[b, x] = top_two(stack_top);
        x = runtime::signextend(b, x);
    }

    // Boolean
    [[gnu::always_inline]] inline void
    lt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a < b;
    }

    [[gnu::always_inline]] inline void
    gt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a > b;
    }

    [[gnu::always_inline]] inline void
    slt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = slt(a, b);
    }

    [[gnu::always_inline]] inline void
    sgt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = slt(b, a); // note swapped arguments
    }

    [[gnu::always_inline]] inline void
    eq(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = (a == b);
    }

    [[gnu::always_inline]] inline void iszero(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &a = *stack_top;
        a = !a;
    }

    // Bitwise
    [[gnu::always_inline]] inline void and_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a & b;
    }

    [[gnu::always_inline]] inline void
    or_(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a | b;
    }

    [[gnu::always_inline]] inline void xor_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[a, b] = top_two(stack_top);
        b = a ^ b;
    }

    [[gnu::always_inline]] inline void not_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &a = *stack_top;
        a = ~a;
    }

    [[gnu::always_inline]] inline void byte(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[i, x] = top_two(stack_top);
        x = runtime::byte(i, x);
    }

    [[gnu::always_inline]] inline void
    shl(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[shift, value] = top_two(stack_top);
        value <<= shift;
    }

    [[gnu::always_inline]] inline void
    shr(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[shift, value] = top_two(stack_top);
        value >>= shift;
    }

    [[gnu::always_inline]] inline void
    sar(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto &&[shift, value] = top_two(stack_top);
        value = runtime::sar(shift, value);
    }

    // Data
    [[gnu::always_inline]] inline void sha3(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::sha3, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void address(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, runtime::uint256_from_address(ctx.env.recipient));
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void balance(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::balance<traits>, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void origin(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_address(ctx.env.tx_context.tx_origin));
    }

    [[gnu::always_inline]] inline void caller(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, runtime::uint256_from_address(ctx.env.sender));
    }

    [[gnu::always_inline]] inline void callvalue(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, runtime::uint256_from_bytes32(ctx.env.value));
    }

    [[gnu::always_inline]] inline void calldataload(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::calldataload, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void calldatasize(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.env.input_data_size);
    }

    [[gnu::always_inline]] inline void calldatacopy(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::calldatacopy, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void codesize(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.env.code_size);
    }

    [[gnu::always_inline]] inline void codecopy(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::codecopy, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void gasprice(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.tx_gas_price));
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void extcodesize(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(
            runtime::extcodesize<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void extcodecopy(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(
            runtime::extcodecopy<traits>, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void returndatasize(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.env.return_data_size);
    }

    [[gnu::always_inline]] inline void returndatacopy(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::returndatacopy, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void extcodehash(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(
            runtime::extcodehash<traits>, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void blockhash(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::blockhash, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void coinbase(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_address(ctx.env.tx_context.block_coinbase));
    }

    [[gnu::always_inline]] inline void timestamp(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.env.tx_context.block_timestamp);
    }

    [[gnu::always_inline]] inline void number(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.env.tx_context.block_number);
    }

    [[gnu::always_inline]] inline void prevrandao(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_bytes32(
                ctx.env.tx_context.block_prev_randao));
    }

    [[gnu::always_inline]] inline void gaslimit(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.env.tx_context.block_gas_limit);
    }

    [[gnu::always_inline]] inline void chainid(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.chain_id));
    }

    [[gnu::always_inline]] inline void selfbalance(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::selfbalance, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void basefee(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.block_base_fee));
    }

    [[gnu::always_inline]] inline void blobhash(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::blobhash, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void blobbasefee(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.blob_base_fee));
    }

    // Memory & Storage
    [[gnu::always_inline]] inline void mload(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::mload, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void mstore(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::mstore, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void mstore8(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::mstore8, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void mcopy(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::mcopy, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void sstore(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::sstore<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void sload(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::sload<traits>, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void tstore(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::tstore, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void tload(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::tload, ctx, stack_top, gas_remaining);
    }

    // Execution Intercode
    [[gnu::always_inline]] inline void
    pc(runtime::Context &, Intercode const &analysis,
       runtime::uint256_t const *, runtime::uint256_t *stack_top,
       std::int64_t &, std::uint8_t const *&instr_ptr)
    {
        push(stack_top, instr_ptr - analysis.code());
    }

    [[gnu::always_inline]] inline void msize(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        push(stack_top, ctx.memory.size);
    }

    [[gnu::always_inline]] inline void
    gas(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        push(stack_top, gas_remaining);
    }

    // Stack
    template <std::size_t N>
        requires(N <= 32)
    [[gnu::always_inline]] inline void push(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining, std::uint8_t const *&instr_ptr)
    {
        push_impl<N>::push(
            ctx, analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);

        instr_ptr += N;
    }

    [[gnu::always_inline]] inline void
    pop(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&)
    {
    }

    template <std::size_t N>
        requires(N >= 1)
    [[gnu::always_inline]] inline void
    dup(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto *const old_top = stack_top;
        push(stack_top, *(old_top - (N - 1)));
    }

    template <std::size_t N>
        requires(N >= 1)
    [[gnu::always_inline]] inline void swap(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &, std::uint8_t const *&)
    {
        auto const top = stack_top->to_avx();
        *stack_top = *(stack_top - N);
        *(stack_top - N) = runtime::uint256_t{top};
    }

    // Control Flow
    namespace
    {
        inline std::uint8_t const *jump_impl(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t const &target)
        {
            if (MONAD_VM_UNLIKELY(
                    target > std::numeric_limits<std::size_t>::max())) {
                ctx.exit(Error);
            }

            auto const jd = static_cast<std::size_t>(target);
            if (MONAD_VM_UNLIKELY(!analysis.is_jumpdest(jd))) {
                ctx.exit(Error);
            }

            return analysis.code() + jd;
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        if constexpr (debug_enabled) {
            trace(analysis, gas_remaining, instr_ptr);
        }
        check_requirements<JUMP, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto const &target = pop(stack_top);
        auto const *const new_ip = jump_impl(ctx, analysis, target);

        MONAD_VM_MUST_TAIL return instruction_table<traits>[*new_ip](
            ctx, analysis, stack_bottom, stack_top, gas_remaining, new_ip);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        if constexpr (debug_enabled) {
            trace(analysis, gas_remaining, instr_ptr);
        }
        check_requirements<JUMPI, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto const &target = pop(stack_top);
        auto const &cond = pop(stack_top);

        if (cond) {
            auto const *const new_ip = jump_impl(ctx, analysis, target);
            MONAD_VM_MUST_TAIL return instruction_table<traits>[*new_ip](
                ctx, analysis, stack_bottom, stack_top, gas_remaining, new_ip);
        }
        else {
            ++instr_ptr;
            MONAD_VM_MUST_TAIL return instruction_table<traits>[*instr_ptr](
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr);
        }
    }

    [[gnu::always_inline]] inline void jumpdest(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&)
    {
    }

    // Logging
    template <std::size_t N>
        requires(N <= 4)
    [[gnu::always_inline]] inline void
    log(runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        static constexpr auto impls = std::tuple{
            &runtime::log0,
            &runtime::log1,
            &runtime::log2,
            &runtime::log3,
            &runtime::log4,
        };
        call_runtime(std::get<N>(impls), ctx, stack_top, gas_remaining);
    }

    // Call & Create
    template <Traits traits>
    [[gnu::always_inline]] inline void create(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::create<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void call(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::call<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void callcode(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::callcode<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void delegatecall(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(
            runtime::delegatecall<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void create2(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(runtime::create2<traits>, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void staticcall(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        call_runtime(
            runtime::staticcall<traits>, ctx, stack_top, gas_remaining);
    }

    // VM Control
    namespace
    {
        inline void return_impl [[noreturn]] (
            runtime::StatusCode const code, runtime::Context &ctx,
            runtime::uint256_t *stack_top, std::int64_t gas_remaining)
        {
            for (auto *result_loc : {&ctx.result.offset, &ctx.result.size}) {
                std::copy_n(
                    stack_top->as_bytes(),
                    32,
                    reinterpret_cast<std::uint8_t *>(result_loc));

                --stack_top;
            }

            ctx.gas_remaining = gas_remaining;
            ctx.exit(code);
        }
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void return_(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining, std::uint8_t const *&)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        check_requirements<RETURN, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        return_impl(Success, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void revert(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining, std::uint8_t const *&)
    {
        check_requirements<REVERT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        return_impl(Revert, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void selfdestruct(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining, std::uint8_t const *&)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        check_requirements<SELFDESTRUCT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        call_runtime(
            runtime::selfdestruct<traits>, ctx, stack_top, gas_remaining);
    }

    [[gnu::always_inline]] inline void stop(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining, std::uint8_t const *&)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Success);
    }

    [[gnu::always_inline]] inline void invalid(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &gas_remaining,
        std::uint8_t const *&)
    {
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Error);
    }
}

#undef MONAD_VM_MUST_TAIL
