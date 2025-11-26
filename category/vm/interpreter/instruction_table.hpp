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

#include <category/core/runtime/uint256.hpp>
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

#define MONAD_VM_NEXT(OP)                                                      \
    do {                                                                       \
        static constexpr auto delta =                                          \
            compiler::opcode_table<traits>[(OP)].stack_increase -              \
            compiler::opcode_table<traits>[(OP)].min_stack;                    \
                                                                               \
        ++instr_ptr;                                                           \
        if constexpr (debug_enabled) {                                         \
            trace(analysis, gas_remaining, instr_ptr);                         \
        }                                                                      \
        MONAD_VM_MUST_TAIL return instruction_table<traits>[*instr_ptr](       \
            ctx,                                                               \
            analysis,                                                          \
            stack_bottom,                                                      \
            stack_top + delta,                                                 \
            gas_remaining,                                                     \
            instr_ptr);                                                        \
    }                                                                          \
    while (false);

#define MONAD_VM_NEXT_PUSH(OP)                                                 \
    do {                                                                       \
        static constexpr auto delta =                                          \
            compiler::opcode_table<traits>[(OP)].stack_increase -              \
            compiler::opcode_table<traits>[(OP)].min_stack;                    \
                                                                               \
        instr_ptr += (((OP) - PUSH0) + 1);                                     \
        if constexpr (debug_enabled) {                                         \
            trace(analysis, gas_remaining, instr_ptr);                         \
        }                                                                      \
        MONAD_VM_MUST_TAIL return instruction_table<traits>[*instr_ptr](       \
            ctx,                                                               \
            analysis,                                                          \
            stack_bottom,                                                      \
            stack_top + delta,                                                 \
            gas_remaining,                                                     \
            instr_ptr);                                                        \
    }                                                                          \
    while (false);

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;
    using enum compiler::EvmOpCode;

    template <Traits traits>
    consteval InstrTable make_instruction_table()
    {
        constexpr auto since = [](evmc_revision first, InstrEval impl) {
            return (traits::evm_rev() >= first) ? impl : invalid;
        };

        return {
            stop, // 0x00
            add<traits>, // 0x01
            mul<traits>, // 0x02
            sub<traits>, // 0x03
            udiv<traits>, // 0x04,
            sdiv<traits>, // 0x05,
            umod<traits>, // 0x06,
            smod<traits>, // 0x07,
            addmod<traits>, // 0x08,
            mulmod<traits>, // 0x09,
            exp<traits>, // 0x0A,
            signextend<traits>, // 0x0B,
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            lt<traits>, // 0x10,
            gt<traits>, // 0x11,
            slt<traits>, // 0x12,
            sgt<traits>, // 0x13,
            eq<traits>, // 0x14,
            iszero<traits>, // 0x15,
            and_<traits>, // 0x16,
            or_<traits>, // 0x17,
            xor_<traits>, // 0x18,
            not_<traits>, // 0x19,
            byte<traits>, // 0x1A,
            since(EVMC_CONSTANTINOPLE, shl<traits>), // 0x1B,
            since(EVMC_CONSTANTINOPLE, shr<traits>), // 0x1C,
            since(EVMC_CONSTANTINOPLE, sar<traits>), // 0x1D,
            since(EVMC_OSAKA, clz<traits>), // 0x1E,
            invalid, //

            sha3<traits>, // 0x20,
            invalid, //
            invalid, //
            invalid, //
            invalid,
            //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            address<traits>, // 0x30,
            balance<traits>, // 0x31,
            origin<traits>, // 0x32,
            caller<traits>, // 0x33,
            callvalue<traits>, // 0x34,
            calldataload<traits>, // 0x35,
            calldatasize<traits>, // 0x36,
            calldatacopy<traits>, // 0x37,
            codesize<traits>, // 0x38,
            codecopy<traits>, // 0x39,
            gasprice<traits>, // 0x3A,
            extcodesize<traits>, // 0x3B,
            extcodecopy<traits>, // 0x3C,
            since(EVMC_BYZANTIUM, returndatasize<traits>), // 0x3D,
            since(EVMC_BYZANTIUM, returndatacopy<traits>), // 0x3E,
            since(EVMC_CONSTANTINOPLE, extcodehash<traits>), // 0x3F,

            blockhash<traits>, // 0x40,
            coinbase<traits>, // 0x41,
            timestamp<traits>, // 0x42,
            number<traits>, // 0x43,
            prevrandao<traits>, // 0x44,
            gaslimit<traits>, // 0x45,
            since(EVMC_ISTANBUL, chainid<traits>), // 0x46,
            since(EVMC_ISTANBUL, selfbalance<traits>), // 0x47,
            since(EVMC_LONDON, basefee<traits>), // 0x48,
            since(EVMC_CANCUN, blobhash<traits>), // 0x49,
            since(EVMC_CANCUN, blobbasefee<traits>), // 0x4A,
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            pop<traits>, // 0x50,
            mload<traits>, // 0x51,
            mstore<traits>, // 0x52,
            mstore8<traits>, // 0x53,
            sload<traits>, // 0x54,
            sstore<traits>, // 0x55,
            jump<traits>, // 0x56,
            jumpi<traits>, // 0x57,
            pc<traits>, // 0x58,
            msize<traits>, // 0x59,
            gas<traits>, // 0x5A,
            jumpdest<traits>, // 0x5B,
            since(EVMC_CANCUN, tload<traits>), // 0x5C,
            since(EVMC_CANCUN, tstore<traits>), // 0x5D,
            since(EVMC_CANCUN, mcopy<traits>), // 0x5E,
            since(EVMC_SHANGHAI, push<0, traits>), // 0x5F,

            push<1, traits>, // 0x60,
            push<2, traits>, // 0x61,
            push<3, traits>, // 0x62,
            push<4, traits>, // 0x63,
            push<5, traits>, // 0x64,
            push<6, traits>, // 0x65,
            push<7, traits>, // 0x66,
            push<8, traits>, // 0x67,
            push<9, traits>, // 0x68,
            push<10, traits>, // 0x69,
            push<11, traits>, // 0x6A,
            push<12, traits>, // 0x6B,
            push<13, traits>, // 0x6C,
            push<14, traits>, // 0x6D,
            push<15, traits>, // 0x6E,
            push<16, traits>, // 0x6F,

            push<17, traits>, // 0x70,
            push<18, traits>, // 0x71,
            push<19, traits>, // 0x72,
            push<20, traits>, // 0x73,
            push<21, traits>, // 0x74,
            push<22, traits>, // 0x75,
            push<23, traits>, // 0x76,
            push<24, traits>, // 0x77,
            push<25, traits>, // 0x78,
            push<26, traits>, // 0x79,
            push<27, traits>, // 0x7A,
            push<28, traits>, // 0x7B,
            push<29, traits>, // 0x7C,
            push<30, traits>, // 0x7D,
            push<31, traits>, // 0x7E,
            push<32, traits>, // 0x7F,

            dup<1, traits>, // 0x80,
            dup<2, traits>, // 0x81,
            dup<3, traits>, // 0x82,
            dup<4, traits>, // 0x83,
            dup<5, traits>, // 0x84,
            dup<6, traits>, // 0x85,
            dup<7, traits>, // 0x86,
            dup<8, traits>, // 0x87,
            dup<9, traits>, // 0x88,
            dup<10, traits>, // 0x89,
            dup<11, traits>, // 0x8A,
            dup<12, traits>, // 0x8B,
            dup<13, traits>, // 0x8C,
            dup<14, traits>, // 0x8D,
            dup<15, traits>, // 0x8E,
            dup<16, traits>, // 0x8F,

            swap<1, traits>, // 0x90,
            swap<2, traits>, // 0x91,
            swap<3, traits>, // 0x92,
            swap<4, traits>, // 0x93,
            swap<5, traits>, // 0x94,
            swap<6, traits>, // 0x95,
            swap<7, traits>, // 0x96,
            swap<8, traits>, // 0x97,
            swap<9, traits>, // 0x98,
            swap<10, traits>, // 0x99,
            swap<11, traits>, // 0x9A,
            swap<12, traits>, // 0x9B,
            swap<13, traits>, // 0x9C,
            swap<14, traits>, // 0x9D,
            swap<15, traits>, // 0x9E,
            swap<16, traits>, // 0x9F,

            log<0, traits>, // 0xA0,
            log<1, traits>, // 0xA1,
            log<2, traits>, // 0xA2,
            log<3, traits>, // 0xA3,
            log<4, traits>, // 0xA4,
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            invalid, //

            create<traits>, // 0xF0,
            call<traits>, // 0xF1,
            callcode<traits>, // 0xF2,
            return_<traits>, // 0xF3,
            since(EVMC_HOMESTEAD, delegatecall<traits>), // 0xF4,
            since(EVMC_CONSTANTINOPLE, create2<traits>), // 0xF5,
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            since(EVMC_BYZANTIUM, staticcall<traits>), // 0xFA,
            invalid, //
            invalid, //
            since(EVMC_BYZANTIUM, revert<traits>), // 0xFD,
            invalid, // 0xFE,
            selfdestruct<traits>, // 0xFF,
        };
    }

    template <Traits traits>
    constexpr InstrTable instruction_table = make_instruction_table<traits>();

    // Instruction implementations
    template <std::uint8_t Opcode, Traits traits, typename... FnArgs>
    [[gnu::always_inline]] inline void checked_runtime_call(
        void (*f)(FnArgs...), runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t &gas_remaining, std::uint8_t const *)
    {
        check_requirements<Opcode, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        call_runtime(f, ctx, stack_top, gas_remaining);
    }

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

    // Arithmetic
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    add(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<ADD, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a + b;

        MONAD_VM_NEXT(ADD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MUL, traits>(
            monad_vm_runtime_mul,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MUL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SUB, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a - b;

        MONAD_VM_NEXT(SUB);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void udiv(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<DIV, traits>(
            runtime::udiv,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(DIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<SDIV, traits>(
            runtime::sdiv,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(SDIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MOD, traits>(
            runtime::umod,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<SMOD, traits>(
            runtime::smod,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(SMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<ADDMOD, traits>(
            runtime::addmod,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(ADDMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MULMOD, traits>(
            runtime::mulmod,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MULMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<EXP, traits>(
            runtime::exp<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(EXP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SIGNEXTEND, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[b, x] = top_two(stack_top);
        x = runtime::signextend(b, x);

        MONAD_VM_NEXT(SIGNEXTEND);
    }

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &ctx, Intercode const &analysis,
       runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
       std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<LT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a < b;

        MONAD_VM_NEXT(LT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gt(runtime::Context &ctx, Intercode const &analysis,
       runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
       std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<GT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a > b;

        MONAD_VM_NEXT(GT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    slt(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SLT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = slt(a, b);

        MONAD_VM_NEXT(SLT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sgt(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SGT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = slt(b, a); // note swapped arguments

        MONAD_VM_NEXT(SGT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    eq(runtime::Context &ctx, Intercode const &analysis,
       runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
       std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<EQ, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = (a == b);

        MONAD_VM_NEXT(EQ);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<ISZERO, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &a = *stack_top;
        a = !a;

        MONAD_VM_NEXT(ISZERO);
    }

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<AND, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a & b;

        MONAD_VM_NEXT(AND);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    or_(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<OR, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a | b;

        MONAD_VM_NEXT(OR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void xor_(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<XOR, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[a, b] = top_two(stack_top);
        b = a ^ b;

        MONAD_VM_NEXT(XOR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void not_(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<NOT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &a = *stack_top;
        a = ~a;

        MONAD_VM_NEXT(NOT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void byte(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<BYTE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[i, x] = top_two(stack_top);
        x = runtime::byte(i, x);

        MONAD_VM_NEXT(BYTE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shl(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SHL, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[shift, value] = top_two(stack_top);
        value <<= shift;

        MONAD_VM_NEXT(SHL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shr(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SHR, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[shift, value] = top_two(stack_top);
        value >>= shift;

        MONAD_VM_NEXT(SHR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sar(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SAR, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto &&[shift, value] = top_two(stack_top);
        value = runtime::sar(shift, value);

        MONAD_VM_NEXT(SAR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    clz(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<CLZ, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);

        auto &value = *stack_top;

        if (value == 0) {
            value = 256;
        }
        else {
            value = runtime::countl_zero(value);
        }

        MONAD_VM_NEXT(CLZ);
    }

    // Data
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sha3(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<SHA3, traits>(
            runtime::sha3,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(SHA3);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<ADDRESS, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, runtime::uint256_from_address(ctx.env.recipient));

        MONAD_VM_NEXT(ADDRESS);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<BALANCE, traits>(
            runtime::balance<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(BALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<ORIGIN, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_address(ctx.env.tx_context.tx_origin));

        MONAD_VM_NEXT(ORIGIN);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void caller(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<CALLER, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, runtime::uint256_from_address(ctx.env.sender));

        MONAD_VM_NEXT(CALLER);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<CALLVALUE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, runtime::uint256_from_bytes32(ctx.env.value));

        MONAD_VM_NEXT(CALLVALUE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CALLDATALOAD, traits>(
            runtime::calldataload,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CALLDATALOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<CALLDATASIZE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.env.input_data_size);

        MONAD_VM_NEXT(CALLDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CALLDATACOPY, traits>(
            runtime::calldatacopy,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CALLDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<CODESIZE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.env.code_size);

        MONAD_VM_NEXT(CODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CODECOPY, traits>(
            runtime::codecopy,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<GASPRICE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.tx_gas_price));

        MONAD_VM_NEXT(GASPRICE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<EXTCODESIZE, traits>(
            runtime::extcodesize<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(EXTCODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<EXTCODECOPY, traits>(
            runtime::extcodecopy<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(EXTCODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<RETURNDATASIZE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.env.return_data_size);

        MONAD_VM_NEXT(RETURNDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<RETURNDATACOPY, traits>(
            runtime::returndatacopy,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(RETURNDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<EXTCODEHASH, traits>(
            runtime::extcodehash<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(EXTCODEHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<BLOCKHASH, traits>(
            runtime::blockhash,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(BLOCKHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<COINBASE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_address(ctx.env.tx_context.block_coinbase));

        MONAD_VM_NEXT(COINBASE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void timestamp(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<TIMESTAMP, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.env.tx_context.block_timestamp);

        MONAD_VM_NEXT(TIMESTAMP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<NUMBER, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.env.tx_context.block_number);

        MONAD_VM_NEXT(NUMBER);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<DIFFICULTY, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_bytes32(
                ctx.env.tx_context.block_prev_randao));

        MONAD_VM_NEXT(DIFFICULTY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gaslimit(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<GASLIMIT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.env.tx_context.block_gas_limit);

        MONAD_VM_NEXT(GASLIMIT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<CHAINID, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.chain_id));

        MONAD_VM_NEXT(CHAINID);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<SELFBALANCE, traits>(
            runtime::selfbalance,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(SELFBALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<BASEFEE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.block_base_fee));

        MONAD_VM_NEXT(BASEFEE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<BLOBHASH, traits>(
            runtime::blobhash,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(BLOBHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<BLOBBASEFEE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(
            stack_top,
            runtime::uint256_from_bytes32(ctx.env.tx_context.blob_base_fee));

        MONAD_VM_NEXT(BLOBBASEFEE);
    }

    // Memory & Storage
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MLOAD, traits>(
            runtime::mload,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MSTORE, traits>(
            runtime::mstore,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MSTORE8, traits>(
            runtime::mstore8,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MSTORE8);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<MCOPY, traits>(
            runtime::mcopy,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(MCOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<SSTORE, traits>(
            runtime::sstore<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(SSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<SLOAD, traits>(
            runtime::sload<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(SLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<TSTORE, traits>(
            runtime::tstore,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(TSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<TLOAD, traits>(
            runtime::tload,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(TLOAD);
    }

    // Execution Intercode
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &ctx, Intercode const &analysis,
       runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
       std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<PC, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, instr_ptr - analysis.code());

        MONAD_VM_NEXT(PC);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<MSIZE, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, ctx.memory.size);

        MONAD_VM_NEXT(MSIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<GAS, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        push(stack_top, gas_remaining);

        MONAD_VM_NEXT(GAS);
    }

    // Stack
    template <std::size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        push_impl<N, traits>::push(
            ctx, analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);

        MONAD_VM_NEXT_PUSH(PUSH0 + N);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<POP, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        MONAD_VM_NEXT(POP);
    }

    template <std::size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<DUP1 + (N - 1), traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);

        auto *const old_top = stack_top;
        push(stack_top, *(old_top - (N - 1)));

        MONAD_VM_NEXT(DUP1 + (N - 1));
    }

    template <std::size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<SWAP1 + (N - 1), traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);

        auto const top = stack_top->to_avx();
        *stack_top = *(stack_top - N);
        *(stack_top - N) = runtime::uint256_t{top};

        MONAD_VM_NEXT(SWAP1 + (N - 1));
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
        std::int64_t gas_remaining, std::uint8_t const *)
    {
        check_requirements<JUMP, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto const &target = pop(stack_top);
        auto const *const new_ip = jump_impl(ctx, analysis, target);

        if constexpr (debug_enabled) {
            trace(analysis, gas_remaining, new_ip);
        }
        MONAD_VM_MUST_TAIL return instruction_table<traits>[*new_ip](
            ctx, analysis, stack_bottom, stack_top, gas_remaining, new_ip);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        check_requirements<JUMPI, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        auto const &target = pop(stack_top);
        auto const &cond = pop(stack_top);

        if (cond) {
            auto const *const new_ip = jump_impl(ctx, analysis, target);
            if constexpr (debug_enabled) {
                trace(analysis, gas_remaining, new_ip);
            }
            MONAD_VM_MUST_TAIL return instruction_table<traits>[*new_ip](
                ctx, analysis, stack_bottom, stack_top, gas_remaining, new_ip);
        }
        else {
            ++instr_ptr;
            if constexpr (debug_enabled) {
                trace(analysis, gas_remaining, instr_ptr);
            }
            MONAD_VM_MUST_TAIL return instruction_table<traits>[*instr_ptr](
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr);
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        fuzz_tstore_stack(
            ctx,
            stack_bottom,
            stack_top,
            static_cast<uint64_t>(instr_ptr - analysis.code()));
        check_requirements<JUMPDEST, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);

        MONAD_VM_NEXT(JUMPDEST);
    }

    // Logging
    template <std::size_t N, Traits traits>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void
    log(runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        static constexpr auto impls = std::tuple{
            &runtime::log0,
            &runtime::log1,
            &runtime::log2,
            &runtime::log3,
            &runtime::log4,
        };

        checked_runtime_call<LOG0 + N, traits>(
            std::get<N>(impls),
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(LOG0 + N);
    }

    // Call & Create
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CREATE, traits>(
            runtime::create<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CREATE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CALL, traits>(
            runtime::call<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CALLCODE, traits>(
            runtime::callcode<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CALLCODE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<DELEGATECALL, traits>(
            runtime::delegatecall<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(DELEGATECALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<CREATE2, traits>(
            runtime::create2<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(CREATE2);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        checked_runtime_call<STATICCALL, traits>(
            runtime::staticcall<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);

        MONAD_VM_NEXT(STATICCALL);
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
    MONAD_VM_INSTRUCTION_CALL void return_(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        check_requirements<RETURN, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        return_impl(Success, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *)
    {
        check_requirements<REVERT, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        return_impl(Revert, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        checked_runtime_call<SELFDESTRUCT, traits>(
            runtime::selfdestruct<traits>,
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr);
    }

    MONAD_VM_INSTRUCTION_CALL inline void stop(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Success);
    }

    MONAD_VM_INSTRUCTION_CALL inline void invalid(
        runtime::Context &ctx, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t gas_remaining, std::uint8_t const *)
    {
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Error);
    }
}

#undef MONAD_VM_MUST_TAIL
#undef MONAD_VM_NEXT
#undef MONAD_VM_NEXT_PUSH
