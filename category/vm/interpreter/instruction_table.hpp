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

#include <category/core/int.hpp>
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

// Evaluate NEXT_OPCODE after advancing instr_ptr; it may be *instr_ptr.
#define MONAD_VM_DISPATCH(NBYTES, DELTA, NEXT_OPCODE)                          \
    do {                                                                       \
        instr_ptr += (NBYTES);                                                 \
        if constexpr (debug_enabled) {                                         \
            trace(analysis, gas_remaining, instr_ptr);                         \
        }                                                                      \
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[(NEXT_OPCODE)](           \
            ctx,                                                               \
            analysis,                                                          \
            stack_bottom,                                                      \
            stack_top + (DELTA),                                               \
            gas_remaining,                                                     \
            instr_ptr MONAD_VM_TBL_ARG);                                       \
    }                                                                          \
    while (false)

// Advance NBYTES and apply the sequence's net stack DELTA before dispatch.
#define MONAD_VM_FUSED_NEXT(NBYTES, DELTA)                                     \
    MONAD_VM_DISPATCH(NBYTES, DELTA, *instr_ptr)

#define MONAD_VM_NEXT_IMPL(OP, NBYTES, NEXT_OPCODE)                            \
    do {                                                                       \
        static constexpr auto delta =                                          \
            compiler::opcode_table<traits>[(OP)].stack_increase -              \
            compiler::opcode_table<traits>[(OP)].min_stack;                    \
        MONAD_VM_DISPATCH(NBYTES, delta, NEXT_OPCODE);                         \
    }                                                                          \
    while (false);

#define MONAD_VM_NEXT(OP) MONAD_VM_NEXT_IMPL(OP, 1, *instr_ptr)

// Expand musttail in the handler to avoid return-address saves on the fast
// path. The guest exits via longjmp, so it does not need the handler's stack
// frame.
#define MONAD_VM_CHECK(OP) MONAD_VM_CHECK_AT(OP, 0)

// Keep checks in the handler so failures can tail-call Context::exit.
// Variadic to accept runtime functions with multiple template arguments.
#define MONAD_VM_CHECKED_RUNTIME_CALL(OP, ...)                                 \
    do {                                                                       \
        MONAD_VM_CHECK(OP);                                                    \
        call_runtime(__VA_ARGS__, ctx, stack_top, gas_remaining);              \
    }                                                                          \
    while (false)

// Check OP after a net stack change of SHIFT from earlier fused opcodes.
#define MONAD_VM_CHECK_AT(OP, SHIFT)                                           \
    MONAD_VM_CHECK_REQUIREMENTS_AT(                                            \
        OP, SHIFT, MONAD_VM_MUST_TAIL return ctx.exit)

#define MONAD_VM_NEXT_PUSH(OP)                                                 \
    MONAD_VM_NEXT_IMPL(OP, ((OP) - PUSH0) + 1, *instr_ptr)

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;
    using enum compiler::EvmOpCode;

#if defined(MONAD_ZKVM_ZISK)
    // After validating the destination, charge JUMPDEST's gas and skip it.
    // Invalid jumps must exit before this charge.
    [[gnu::always_inline]] inline uint8_t const *swallow_jumpdest(
        runtime::Context &ctx, uint8_t const *landing, int64_t &gas_remaining)
    {
        gas_remaining -= 1;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }
        return landing + 1;
    }

    // Complete <test> PUSH2 JUMPI using the test result directly.
    // Jump to the validated destination encoded at p[2..3], or skip five bytes.
    [[gnu::always_inline]] inline uint8_t const *fused_branch(
        runtime::Context &ctx, Intercode const &analysis, uint8_t const *p,
        bool taken, int64_t &gas_remaining)
    {
        // Condition is false; continue after the sequence.
        if (!taken) {
            return p + 5;
        }
        auto const dst = static_cast<size_t>(
            (static_cast<unsigned>(p[2]) << 8) | static_cast<unsigned>(p[3]));
        if (MONAD_UNLIKELY(!analysis.is_jumpdest(dst))) {
            ctx.exit(Error);
        }
        auto const *ip = analysis.code() + dst;
        ip = swallow_jumpdest(ctx, ip, gas_remaining);
        return ip;
    }
#endif

    template <Traits traits>
    consteval InstrTable make_instruction_table()
    {
        static_assert(traits::evm_rev() >= MONAD_ETH_ISTANBUL);

        constexpr auto avail = [](compiler::EvmOpCode const opcode,
                                  InstrEval impl) {
            return !compiler::is_unknown_opcode_info<traits>(opcode) ? impl
                                                                     : invalid;
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
            shl<traits>, // 0x1B,
            shr<traits>, // 0x1C,
            sar<traits>, // 0x1D,
            avail(CLZ, clz<traits>), // 0x1E,
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
            returndatasize<traits>, // 0x3D,
            returndatacopy<traits>, // 0x3E,
            extcodehash<traits>, // 0x3F,

            blockhash<traits>, // 0x40,
            coinbase<traits>, // 0x41,
            timestamp<traits>, // 0x42,
            number<traits>, // 0x43,
            prevrandao<traits>, // 0x44,
            gaslimit<traits>, // 0x45,
            chainid<traits>, // 0x46,
            selfbalance<traits>, // 0x47,
            avail(BASEFEE, basefee<traits>), // 0x48,
            avail(BLOBHASH, blobhash<traits>), // 0x49,
            avail(BLOBBASEFEE, blobbasefee<traits>), // 0x4A,
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
            avail(TLOAD, tload<traits>), // 0x5C,
            avail(TSTORE, tstore<traits>), // 0x5D,
            avail(MCOPY, mcopy<traits>), // 0x5E,
            avail(PUSH0, push<0, traits>), // 0x5F,

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
            delegatecall<traits>, // 0xF4,
            create2<traits>, // 0xF5,
            invalid, //
            invalid, //
            invalid, //
            invalid, //
            staticcall<traits>, // 0xFA,
            invalid, //
            invalid, //
            revert<traits>, // 0xFD,
            invalid, // 0xFE,
            selfdestruct<traits>, // 0xFF,
        };
    }

    template <Traits traits>
    constexpr InstrTable instruction_table = make_instruction_table<traits>();

    // Instruction implementations
#ifdef MONAD_COMPILER_TESTING
    [[gnu::always_inline]]
    inline void fuzz_tstore_stack(
        runtime::Context const &ctx, uint256_t const *stack_bottom,
        uint256_t const *stack_top, uint64_t const base_offset)
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
        runtime::Context const &, uint256_t const *, uint256_t const *,
        uint64_t const)
    {
        // nop
    }
#endif

    // Arithmetic
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    add(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ADD);
        auto &&[a, b] = top_two(stack_top);
#if defined(MONAD_ZKVM_ZISK)
        // Let the precompile handle the 256-bit addition and carries.
        zisk_add256(ctx.add256_params, ctx.add256_out, a, b, b);
#else
        b = a + b;
#endif

        MONAD_VM_NEXT(ADD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MUL, runtime::mul);

        MONAD_VM_NEXT(MUL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SUB);
        auto &&[a, b] = top_two(stack_top);
        b = a - b;

        MONAD_VM_NEXT(SUB);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void udiv(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(DIV, runtime::udiv);

        MONAD_VM_NEXT(DIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SDIV, runtime::sdiv);

        MONAD_VM_NEXT(SDIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MOD, runtime::umod);

        MONAD_VM_NEXT(MOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SMOD, runtime::smod);

        MONAD_VM_NEXT(SMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(ADDMOD, runtime::addmod);

        MONAD_VM_NEXT(ADDMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MULMOD, runtime::mulmod);

        MONAD_VM_NEXT(MULMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(EXP, runtime::exp<traits>);

        MONAD_VM_NEXT(EXP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SIGNEXTEND);
        auto &&[b, x] = top_two(stack_top);
        x = signextend(b, x);

        MONAD_VM_NEXT(SIGNEXTEND);
    }

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &ctx, Intercode const &analysis,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(LT);
        auto &&[a, b] = top_two(stack_top);
        b = a < b;

        MONAD_VM_NEXT(LT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gt(runtime::Context &ctx, Intercode const &analysis,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GT);
        auto &&[a, b] = top_two(stack_top);
        b = a > b;

        MONAD_VM_NEXT(GT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    slt(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SLT);
        auto &&[a, b] = top_two(stack_top);
        b = slt(a, b);

        MONAD_VM_NEXT(SLT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sgt(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SGT);
        auto &&[a, b] = top_two(stack_top);
        b = slt(b, a); // note swapped arguments

        MONAD_VM_NEXT(SGT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    eq(runtime::Context &ctx, Intercode const &analysis,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse EQ PUSH2 <dst16> JUMPI. EQ frees a stack slot, so PUSH2
        // cannot overflow once EQ's operands are validated.
        if (*(instr_ptr + 1) == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            MONAD_VM_CHECK(EQ);
            // EQ consumes two values and pushes one result: net stack change
            // -1.
            MONAD_VM_CHECK_AT(PUSH2, -1);
            // PUSH2 adds one value, restoring the original stack height.
            MONAD_VM_CHECK_AT(JUMPI, 0);
            // Keep EQ's result in a C++ bool instead of the EVM stack.
            bool const monad_vm_taken = (*stack_top == *(stack_top - 1));
            instr_ptr = fused_branch(
                ctx, analysis, instr_ptr, monad_vm_taken, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                analysis,
                stack_bottom,
                stack_top - 2,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(EQ);
        auto &&[a, b] = top_two(stack_top);
        b = (a == b);

        MONAD_VM_NEXT(EQ);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse ISZERO PUSH2 <dst16> JUMPI without storing the test result.
        if (*(instr_ptr + 1) == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            MONAD_VM_CHECK(ISZERO);
            MONAD_VM_CHECK_AT(PUSH2, 0);
            MONAD_VM_CHECK_AT(JUMPI, 1);
            bool const monad_vm_taken = !*stack_top;
            instr_ptr = fused_branch(
                ctx, analysis, instr_ptr, monad_vm_taken, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                analysis,
                stack_bottom,
                stack_top - 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(ISZERO);
        auto &a = *stack_top;
        a = !a;

        MONAD_VM_NEXT(ISZERO);
    }

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(AND);
        auto &&[a, b] = top_two(stack_top);
        b = a & b;

        MONAD_VM_NEXT(AND);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    or_(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(OR);
        auto &&[a, b] = top_two(stack_top);
        b = a | b;

        MONAD_VM_NEXT(OR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void xor_(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(XOR);
        auto &&[a, b] = top_two(stack_top);
        b = a ^ b;

        MONAD_VM_NEXT(XOR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void not_(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(NOT);
        auto &a = *stack_top;
        a = ~a;

        MONAD_VM_NEXT(NOT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void byte(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BYTE);
        auto &&[i, x] = top_two(stack_top);
        x = byte(i, x);

        MONAD_VM_NEXT(BYTE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shl(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SHL);
        auto &&[shift, value] = top_two(stack_top);
        value <<= shift;

        MONAD_VM_NEXT(SHL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shr(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SHR);
        auto &&[shift, value] = top_two(stack_top);
        value >>= shift;

        MONAD_VM_NEXT(SHR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sar(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SAR);
        auto &&[shift, value] = top_two(stack_top);
        value = sar(shift, value);

        MONAD_VM_NEXT(SAR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    clz(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CLZ);
        auto &a = *stack_top;
        a = countl_zero(a);

        MONAD_VM_NEXT(CLZ);
    }

    // Data
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sha3(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SHA3, runtime::sha3<traits>);

        MONAD_VM_NEXT(SHA3);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ADDRESS);
        push(stack_top, runtime::uint256_from_address(ctx.env.recipient));

        MONAD_VM_NEXT(ADDRESS);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BALANCE, runtime::balance<traits>);

        MONAD_VM_NEXT(BALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ORIGIN);
        push(
            stack_top,
            runtime::uint256_from_address(ctx.env.tx_context->tx_origin));

        MONAD_VM_NEXT(ORIGIN);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void caller(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CALLER);
        push(stack_top, runtime::uint256_from_address(ctx.env.sender));

        MONAD_VM_NEXT(CALLER);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CALLVALUE);
        push(stack_top, load_be<uint256_t>(ctx.env.value));

        MONAD_VM_NEXT(CALLVALUE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALLDATALOAD, runtime::calldataload);

        MONAD_VM_NEXT(CALLDATALOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CALLDATASIZE);
        push(stack_top, ctx.env.input_data_size);

        MONAD_VM_NEXT(CALLDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CALLDATACOPY, runtime::calldatacopy<traits>);

        MONAD_VM_NEXT(CALLDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CODESIZE);
        push(stack_top, ctx.env.code_size);

        MONAD_VM_NEXT(CODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CODECOPY, runtime::codecopy<traits>);

        MONAD_VM_NEXT(CODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GASPRICE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->tx_gas_price));

        MONAD_VM_NEXT(GASPRICE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODESIZE, runtime::extcodesize<traits>);

        MONAD_VM_NEXT(EXTCODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODECOPY, runtime::extcodecopy<traits>);

        MONAD_VM_NEXT(EXTCODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(RETURNDATASIZE);
        push(stack_top, ctx.env.return_data_size);

        MONAD_VM_NEXT(RETURNDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            RETURNDATACOPY, runtime::returndatacopy<traits>);

        MONAD_VM_NEXT(RETURNDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODEHASH, runtime::extcodehash<traits>);

        MONAD_VM_NEXT(EXTCODEHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BLOCKHASH, runtime::blockhash);

        MONAD_VM_NEXT(BLOCKHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(COINBASE);
        push(
            stack_top,
            runtime::uint256_from_address(ctx.env.tx_context->block_coinbase));

        MONAD_VM_NEXT(COINBASE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void timestamp(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(TIMESTAMP);
        push(stack_top, ctx.env.tx_context->block_timestamp);

        MONAD_VM_NEXT(TIMESTAMP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(NUMBER);
        push(stack_top, ctx.env.tx_context->block_number);

        MONAD_VM_NEXT(NUMBER);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(DIFFICULTY);
        push(
            stack_top,
            load_be<uint256_t>(ctx.env.tx_context->block_prev_randao));

        MONAD_VM_NEXT(DIFFICULTY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gaslimit(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GASLIMIT);
        push(stack_top, ctx.env.tx_context->block_gas_limit);

        MONAD_VM_NEXT(GASLIMIT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CHAINID);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->chain_id));

        MONAD_VM_NEXT(CHAINID);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SELFBALANCE, runtime::selfbalance);

        MONAD_VM_NEXT(SELFBALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BASEFEE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->block_base_fee));

        MONAD_VM_NEXT(BASEFEE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BLOBHASH, runtime::blobhash);

        MONAD_VM_NEXT(BLOBHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BLOBBASEFEE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->blob_base_fee));

        MONAD_VM_NEXT(BLOBBASEFEE);
    }

    // Memory & Storage

    // Isolate rare memory growth to avoid register spills on MLOAD's fast path.
    // Continue dispatch here instead of returning to mload. Gas and stack
    // checks have already run; do not repeat them.
    // This split regressed MSTORE, where memory growth is more frequent.
    template <Traits traits>
    [[gnu::noinline, gnu::cold]] MONAD_VM_INSTRUCTION_CALL void mload_grow(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        call_runtime(runtime::mload<traits>, ctx, stack_top, gas_remaining);

        MONAD_VM_NEXT(MLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(MLOAD);

        ctx.gas_remaining = gas_remaining;
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mload_grow<traits>(
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        runtime::mload_at<traits>(&ctx, stack_top, offset);
        gas_remaining = ctx.gas_remaining;

        MONAD_VM_NEXT(MLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MSTORE, runtime::mstore<traits>);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MSTORE8, runtime::mstore8<traits>);

        MONAD_VM_NEXT(MSTORE8);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MCOPY, runtime::mcopy<traits>);

        MONAD_VM_NEXT(MCOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SSTORE, runtime::sstore<traits>);

        MONAD_VM_NEXT(SSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SLOAD, runtime::sload<traits>);

        MONAD_VM_NEXT(SLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(TSTORE, runtime::tstore);

        MONAD_VM_NEXT(TSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(TLOAD, runtime::tload);

        MONAD_VM_NEXT(TLOAD);
    }

    // Execution Intercode
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &ctx, Intercode const &analysis,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(PC);
        push(stack_top, instr_ptr - analysis.code());

        MONAD_VM_NEXT(PC);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(MSIZE);
        push(stack_top, ctx.memory.size);

        MONAD_VM_NEXT(MSIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GAS);
        push(stack_top, gas_remaining);

        MONAD_VM_NEXT(GAS);
    }

    // Stack
    template <size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Use PUSH1's immediate directly for ADD/SHL/SHR/SAR.
        // The result replaces the top; the pair's net stack change is zero.
        // Check PUSH1 before its follower, including temporary stack growth.
        // Code padding makes the lookahead safe.
        if constexpr (N == 1) {
            // A bitmap keeps the check cheap on every PUSH1; testing four
            // opcodes separately regressed performance.
            constexpr std::uint64_t monad_vm_fuse_mask =
                (1ull << static_cast<unsigned>(ADD)) |
                (1ull << static_cast<unsigned>(SHL)) |
                (1ull << static_cast<unsigned>(SHR)) |
                (1ull << static_cast<unsigned>(SAR));
            // PUSH1 and DUP2 exceed the mask's range and still need stack
            // writes, so their fusions are omitted.
            auto const monad_vm_op2 = *(instr_ptr + 2);
            // Filtering for these four opcodes first improves performance.
            if (monad_vm_op2 < 64 &&
                ((monad_vm_fuse_mask >> monad_vm_op2) & 1)) {
                MONAD_VM_CHECK(PUSH1);
                uint256_t const monad_vm_imm{*(instr_ptr + 1)};
                if (monad_vm_op2 == static_cast<std::uint8_t>(ADD)) {
                    MONAD_VM_CHECK_AT(ADD, 1);
                    *stack_top = monad_vm_imm + *stack_top;
                }
                else if (monad_vm_op2 == static_cast<std::uint8_t>(SHL)) {
                    MONAD_VM_CHECK_AT(SHL, 1);
                    *stack_top <<= monad_vm_imm;
                }
                else if (monad_vm_op2 == static_cast<std::uint8_t>(SHR)) {
                    MONAD_VM_CHECK_AT(SHR, 1);
                    *stack_top >>= monad_vm_imm;
                }
                else {
                    MONAD_VM_CHECK_AT(SAR, 1);
                    *stack_top = sar(monad_vm_imm, *stack_top);
                }
                // Advance instr_ptr by 3 bytes, keep the stack size unchanged,
                // and call the next opcode handler.
                // Returns from the current handler.
                MONAD_VM_FUSED_NEXT(3, 0);
            }
        }
        // Use PUSH2's immediate directly as the JUMP/JUMPI destination.
        // Check gas and stack in opcode order, then validate taken jumps.
        if constexpr (N == 2) {
            auto const monad_vm_op2 = *(instr_ptr + 3);
            // Match JUMP and JUMPI with one range check: they are consecutive.
            // size_t and not unsigned for the difference: a 32-bit subtract
            // puts this on ZisK's generic binary machine on every PUSH2.
            if (static_cast<size_t>(monad_vm_op2) - static_cast<size_t>(JUMP) <=
                1u) {
                MONAD_VM_CHECK(PUSH2);
                // PUSH2's two-byte immediate gives the jump destination.
                auto const monad_vm_dst = static_cast<size_t>(
                    (static_cast<unsigned>(*(instr_ptr + 1)) << 8) |
                    static_cast<unsigned>(*(instr_ptr + 2)));
                if (monad_vm_op2 == static_cast<std::uint8_t>(JUMP)) {
                    // Check gas and stack as if PUSH2 had added one item.
                    MONAD_VM_CHECK_AT(JUMP, 1);
                    if (MONAD_UNLIKELY(!analysis.is_jumpdest(monad_vm_dst))) {
                        ctx.exit(Error);
                    }
                    auto const *monad_vm_ip = analysis.code() + monad_vm_dst;
                    monad_vm_ip =
                        swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
                    instr_ptr = monad_vm_ip;
                    MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                        ctx,
                        analysis,
                        stack_bottom,
                        stack_top,
                        gas_remaining,
                        instr_ptr MONAD_VM_TBL_ARG);
                }
                MONAD_VM_CHECK_AT(JUMPI, 1);
                // The condition is the original top, below PUSH2's destination.
                if (*stack_top) {
                    if (MONAD_UNLIKELY(!analysis.is_jumpdest(monad_vm_dst))) {
                        ctx.exit(Error);
                    }
                    auto const *monad_vm_ip = analysis.code() + monad_vm_dst;
                    monad_vm_ip =
                        swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
                    instr_ptr = monad_vm_ip;
                    MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                        ctx,
                        analysis,
                        stack_bottom,
                        stack_top - 1, // Consume JUMPI's condition.
                        gas_remaining,
                        instr_ptr MONAD_VM_TBL_ARG);
                }
                // Advance instr_ptr by 4 bytes, reduce the stack size by 1 to
                // consume JUMPI's condition, and call the next opcode handler.
                // Returns from the current handler.
                MONAD_VM_FUSED_NEXT(4, -1);
            }
        }
#endif
        MONAD_VM_CHECK(PUSH0 + N);
        push_impl<N, traits>::push(stack_top, instr_ptr);

        MONAD_VM_NEXT_PUSH(PUSH0 + N);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(POP);
        MONAD_VM_NEXT(POP);
    }

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(DUP1 + (N - 1));

        auto *const old_top = stack_top;
        push(stack_top, *(old_top - (N - 1)));

        MONAD_VM_NEXT(DUP1 + (N - 1));
    }

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SWAP1 + (N - 1));

        auto const top = stack_top->to_avx();
        *stack_top = *(stack_top - N);
        *(stack_top - N) = uint256_t{top};

        MONAD_VM_NEXT(SWAP1 + (N - 1));
    }

    // Control Flow
    namespace
    {
        inline uint8_t const *jump_impl(
            runtime::Context &ctx, Intercode const &analysis,
            uint256_t const &target)
        {
            if (MONAD_UNLIKELY(target > std::numeric_limits<size_t>::max())) {
                ctx.exit(Error);
            }

            auto const jd = static_cast<size_t>(target);
            if (MONAD_UNLIKELY(!analysis.is_jumpdest(jd))) {
                ctx.exit(Error);
            }

            return analysis.code() + jd;
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(JUMP);
        auto const &target = pop(stack_top);
        auto const *new_ip = jump_impl(ctx, analysis, target);
#if defined(MONAD_ZKVM_ZISK)
        new_ip = swallow_jumpdest(ctx, new_ip, gas_remaining);
#endif

        if constexpr (debug_enabled) {
            trace(analysis, gas_remaining, new_ip);
        }
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
            ctx,
            analysis,
            stack_bottom,
            stack_top,
            gas_remaining,
            new_ip MONAD_VM_TBL_ARG);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(JUMPI);
        auto const &target = pop(stack_top);
        auto const &cond = pop(stack_top);

        if (cond) {
            auto const *new_ip = jump_impl(ctx, analysis, target);
#if defined(MONAD_ZKVM_ZISK)
            new_ip = swallow_jumpdest(ctx, new_ip, gas_remaining);
#endif
            if constexpr (debug_enabled) {
                trace(analysis, gas_remaining, new_ip);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                new_ip MONAD_VM_TBL_ARG);
        }
        else {
            ++instr_ptr;
            if constexpr (debug_enabled) {
                trace(analysis, gas_remaining, instr_ptr);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        fuzz_tstore_stack(
            ctx,
            stack_bottom,
            stack_top,
            static_cast<uint64_t>(instr_ptr - analysis.code()));
        MONAD_VM_CHECK(JUMPDEST);

        MONAD_VM_NEXT(JUMPDEST);
    }

    // Logging
    template <size_t N, Traits traits>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void
    log(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        static constexpr auto impls = std::tuple{
            &runtime::log0<traits>,
            &runtime::log1<traits>,
            &runtime::log2<traits>,
            &runtime::log3<traits>,
            &runtime::log4<traits>,
        };

        MONAD_VM_CHECKED_RUNTIME_CALL(LOG0 + N, std::get<N>(impls));

        MONAD_VM_NEXT(LOG0 + N);
    }

    // Call & Create
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CREATE, runtime::create<traits>);

        MONAD_VM_NEXT(CREATE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALL, runtime::call<traits>);

        MONAD_VM_NEXT(CALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALLCODE, runtime::callcode<traits>);

        MONAD_VM_NEXT(CALLCODE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            DELEGATECALL, runtime::delegatecall<traits>);

        MONAD_VM_NEXT(DELEGATECALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CREATE2, runtime::create2<traits>);

        MONAD_VM_NEXT(CREATE2);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(STATICCALL, runtime::staticcall<traits>);

        MONAD_VM_NEXT(STATICCALL);
    }

    // VM Control
    namespace
    {
        inline void return_impl [[noreturn]] (
            runtime::StatusCode const code, runtime::Context &ctx,
            uint256_t *stack_top, int64_t const gas_remaining)
        {
            for (auto *result_loc : {&ctx.result.offset, &ctx.result.size}) {
                std::copy_n(
                    as_bytes(*stack_top),
                    32,
                    reinterpret_cast<uint8_t *>(result_loc));

                --stack_top;
            }

            ctx.gas_remaining = gas_remaining;
            ctx.exit(code);
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void return_(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        MONAD_VM_CHECK(RETURN);
        return_impl(Success, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        MONAD_VM_CHECK(REVERT);
        return_impl(Revert, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SELFDESTRUCT, runtime::selfdestruct<traits>);
    }

    MONAD_VM_INSTRUCTION_CALL inline void stop(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *const stack_bottom, uint256_t *const stack_top,
        int64_t const gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Success);
    }

    MONAD_VM_INSTRUCTION_CALL inline void invalid(
        runtime::Context &ctx, Intercode const &, uint256_t const *,
        uint256_t *, int64_t const gas_remaining,
        uint8_t const *MONAD_VM_TBL_TYPE)
    {
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Error);
    }
}

#undef MONAD_VM_MUST_TAIL
#undef MONAD_VM_DISPATCH
#undef MONAD_VM_FUSED_NEXT
#undef MONAD_VM_NEXT_IMPL
#undef MONAD_VM_NEXT
#undef MONAD_VM_NEXT_PUSH
#undef MONAD_VM_CHECK
#undef MONAD_VM_CHECK_AT
#undef MONAD_VM_CHECKED_RUNTIME_CALL
