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
#include <category/vm/interpreter/stack_top.hpp>
#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/runtime.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/utils/debug.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>

#if defined(__has_attribute)
    #if __has_attribute(musttail)
        #define MONAD_VM_MUST_TAIL __attribute__((musttail))
    #else
        #error "No compiler support for __attribute__((musttail))"
    #endif
#else
    #error "No compiler support for __has_attribute"
#endif

#if defined(MONAD_ZKVM_ZISK)
// Make the next load use the advanced pointer, so GCC need not keep the
// old pointer in another register. The empty asm emits no instruction.
    #define MONAD_VM_LAUNDER(P) asm("" : "+r"(P))
#else
    #define MONAD_VM_LAUNDER(P)
#endif

namespace monad::vm::interpreter
{
    // Encourage GCC to keep ctx in its incoming register (a0 on ZisK),
    // avoiding save/restore copies around temporary operands.
    [[gnu::always_inline]] inline runtime::Context &
    held_in_a0(runtime::Context &ctx) noexcept
    {
        auto *p = &ctx;
        MONAD_VM_LAUNDER(p);
        return *p;
    }

#if defined(MONAD_ZKVM_ZISK)
    // The linker places handlers in opcode order, in 1 << slot_shift byte slots.
    // Dispatch computes base + (opcode << slot_shift), without a pointer lookup.
    inline constexpr size_t slot_shift = 10;

    // Two entry points inside each existing fixed-size slot:
    // [PUSH1 prefix: 32 bytes][normal handler][optional fused pair]
    //  ^ PUSH1 followed by OP  ^ OP alone
    // The prefix executes the pending PUSH1, or jumps to a fused pair.
    // Normal dispatch skips it; execute.cpp and the linker share this size.
    inline constexpr size_t push1_prefix_size = 32;

    // Jump to the follower's PUSH1 prefix with the handler arguments in a0-a6.
    // Encoding -push1_prefix_size in jalr avoids a separate address adjustment.
    #define MONAD_VM_PUSH1_PREFIX_DISPATCH(NEXT_OPCODE, TOP, GAS, IP)          \
        do {                                                                   \
            auto const follower_handler_address =                              \
                reinterpret_cast<uintptr_t>(table_base) +                      \
                (static_cast<uintptr_t>(NEXT_OPCODE) << slot_shift);           \
            register runtime::Context *monad_vm_a0 asm("a0") = &ctx;           \
            register uint256_t const *monad_vm_a1 asm("a1") =                  \
                MONAD_VM_DISPATCH_STATE_ARG;                                   \
            register uint256_t const *monad_vm_a2 asm("a2") =                  \
                stack_lower_bound;                                             \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP).next_slot();     \
            register int64_t monad_vm_a4 asm("a4") = (GAS);                    \
            register uint8_t const *monad_vm_a5 asm("a5") = (IP);              \
            register void const *monad_vm_a6 asm("a6") = table_base;           \
            asm volatile("jalr zero, %[off](%[head])"                          \
                         :                                                     \
                         : [head] "r"(follower_handler_address),               \
                           [off] "i"(-static_cast<int>(push1_prefix_size)),    \
                           "r"(monad_vm_a0),                                   \
                           "r"(monad_vm_a1),                                   \
                           "r"(monad_vm_a2),                                   \
                           "r"(monad_vm_a3),                                   \
                           "r"(monad_vm_a4),                                   \
                           "r"(monad_vm_a5),                                   \
                           "r"(monad_vm_a6)                                    \
                         : "memory");                                          \
            __builtin_unreachable();                                           \
        }                                                                      \
        while (false)

    // The revisions whose handlers have slots: the EVM ones the guest runs.
    // Other traits dispatch through their table.
    template <Traits traits>
    inline constexpr bool has_slots =
        std::is_same_v<traits, EvmTraits<traits::evm_rev()>> &&
        traits::evm_rev() >= EvmRevision::Berlin &&
        traits::evm_rev() <= EvmRevision::Amsterdam;

    struct SlotTable
    {
        void const *base;

        [[gnu::always_inline]] InstrEval
        operator[](size_t const opcode) const noexcept
        {
            return reinterpret_cast<InstrEval>(
                reinterpret_cast<uintptr_t>(base) + (opcode << slot_shift));
        }
    };

    // What MONAD_VM_TABLE_REF indexes: the slots' base, or the table.
    template <Traits traits>
    [[gnu::always_inline]] inline auto
    dispatch_table(void const *const table_base) noexcept
    {
        if constexpr (has_slots<traits>) {
            return SlotTable{table_base};
        }
        else {
            return static_cast<InstrEval const *>(table_base);
        }
    }
#endif
}

// Evaluate NEXT_OPCODE after advancing instr_ptr; it may be *instr_ptr.
#define MONAD_VM_DISPATCH(NBYTES, STACK_DELTA, NEXT_OPCODE)                    \
    do {                                                                       \
        instr_ptr += (NBYTES);                                                 \
        MONAD_VM_LAUNDER(instr_ptr);                                           \
        if constexpr (debug_enabled) {                                         \
            trace(MONAD_VM_CODE_VIEW, gas_remaining, instr_ptr);               \
        }                                                                      \
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[(NEXT_OPCODE)](           \
            ctx,                                                               \
            MONAD_VM_DISPATCH_STATE_ARG,                                       \
            stack_lower_bound,                                                 \
            stack_top + (STACK_DELTA),                                         \
            gas_remaining,                                                     \
            instr_ptr MONAD_VM_TBL_ARG);                                       \
    }                                                                          \
    while (false)

// Advance NBYTES through bytecode and STACK_DELTA slots on the EVM stack.
#define MONAD_VM_FUSED_NEXT(NBYTES, STACK_DELTA)                               \
    MONAD_VM_DISPATCH(NBYTES, STACK_DELTA, *instr_ptr)

#define MONAD_VM_NEXT_IMPL(OP, NBYTES, NEXT_OPCODE)                            \
    do {                                                                       \
        static constexpr auto delta =                                          \
            compiler::opcode_table<traits>[(OP)].stack_increase -               \
            compiler::opcode_table<traits>[(OP)].min_stack;                    \
        MONAD_VM_DISPATCH(NBYTES, delta, NEXT_OPCODE);                         \
    }                                                                          \
    while (false);

#define MONAD_VM_NEXT(OP) MONAD_VM_NEXT_IMPL(OP, 1, *instr_ptr)
#define MONAD_VM_NEXT_IMM(OP) MONAD_VM_NEXT_IMPL(OP, 2, *instr_ptr)

// Expand musttail in the handler to avoid return-address saves on the fast
// path. The guest exits via longjmp, so it does not need the handler's stack
// frame.
#define MONAD_VM_CHECK(OP) MONAD_VM_CHECK_AT(OP, 0)

// Keep checks in the handler so failures can tail-call Context::exit.
// Variadic to accept runtime functions with multiple template arguments.
#if defined(MONAD_ZKVM_ZISK)
// Reload bounds after context-taking runtimes so host calls need not preserve
// them in saved registers. Context-free arithmetic keeps the register values.
    #define MONAD_VM_CHECKED_RUNTIME_CALL(OP, ...)                             \
        do {                                                                   \
            MONAD_VM_CHECK(OP);                                                \
            call_runtime(__VA_ARGS__, ctx, stack_top, gas_remaining);          \
            if constexpr (::monad::vm::interpreter::                           \
                              runtime_function_uses_context<std::decay_t<      \
                                  decltype(__VA_ARGS__)>>::value) {            \
                stack_lower_bound = ctx.frame_stack_lower_bound;               \
                stack_limit = ctx.stack_limit;                                 \
            }                                                                  \
        }                                                                      \
        while (false)
#else
    #define MONAD_VM_CHECKED_RUNTIME_CALL(OP, ...)                             \
        do {                                                                   \
            MONAD_VM_CHECK(OP);                                                \
            call_runtime(__VA_ARGS__, ctx, stack_top, gas_remaining);          \
        }                                                                      \
        while (false)
#endif

// Check OP after a net stack change of SHIFT from earlier fused opcodes.
#define MONAD_VM_CHECK_AT(OP, SHIFT)                                           \
    MONAD_VM_CHECK_REQUIREMENTS_AT(                                            \
        OP, SHIFT, MONAD_VM_MUST_TAIL return ctx.exit)

#if defined(MONAD_ZKVM_ZISK)
// Separate selected error exits so GCC need not merge them and keep an extra
// copy of ctx. Apply only to DUP2-16 overflow and MLOAD/MSTORE base gas checks.
    #define MONAD_VM_EXIT_OWN_OUT_OF_GAS(CODE)                                 \
        MONAD_VM_MUST_TAIL return ::monad::vm::interpreter::exit_out_of_gas(ctx)
    #define MONAD_VM_EXIT_OWN_OVERFLOW(CODE)                                   \
        MONAD_VM_MUST_TAIL return ::monad::vm::interpreter::                   \
            exit_stack_overflow(ctx)
    #define MONAD_VM_CHECK_OWN_OVERFLOW(OP)                                    \
        MONAD_VM_CHECK_REQUIREMENTS_AT_EXITS(                                  \
            OP,                                                                \
            0,                                                                 \
            MONAD_VM_MUST_TAIL return ctx.exit,                                \
            MONAD_VM_MUST_TAIL return ctx.exit,                                \
            MONAD_VM_EXIT_OWN_OVERFLOW)
    #define MONAD_VM_CHECK_OWN_GAS(OP)                                         \
        MONAD_VM_CHECK_REQUIREMENTS_AT_EXITS(                                  \
            OP,                                                                \
            0,                                                                 \
            MONAD_VM_MUST_TAIL return ctx.exit,                                \
            MONAD_VM_EXIT_OWN_OUT_OF_GAS,                                      \
            MONAD_VM_MUST_TAIL return ctx.exit)
#else
    #define MONAD_VM_CHECK_OWN_OVERFLOW(OP) MONAD_VM_CHECK(OP)
    #define MONAD_VM_CHECK_OWN_GAS(OP) MONAD_VM_CHECK(OP)
#endif

// Charge gas only. Each caller must justify why its stack checks cannot fail.
#define MONAD_VM_CHARGE(OP)                                                    \
    do {                                                                       \
        static constexpr auto monad_vm_ci =                                    \
            compiler::opcode_table<traits>[(OP)];                              \
                                                                               \
        if constexpr (monad_vm_ci.min_gas > 0) {                               \
            gas_remaining -= monad_vm_ci.min_gas;                              \
            if (MONAD_UNLIKELY(gas_remaining < 0)) {                           \
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);                  \
            }                                                                  \
        }                                                                      \
    }                                                                          \
    while (false)

// Charge the total gas, then check the stack. On failure the caller gives the
// charge back, and per-opcode checks preserve error order and gas accounting.
// Unneeded stack bounds compile away.
#define MONAD_VM_FUSED_CHARGE(REQ)                                             \
    (::monad::vm::interpreter::charge_gas(gas_remaining, (REQ).gas) &&         \
     ::monad::vm::interpreter::stack_holds<(REQ).min_required>(                \
         stack_top, stack_lower_bound) &&                                      \
     ((REQ).max_growth == 0 ||                                                 \
      stack_top.next_slot() < MONAD_VM_STACK_LIMIT + (1 - (REQ).max_growth)))

// Charge gas now; pure sequences check it at the next checkpoint.
// Fused JUMPI checks at the landing JUMPDEST if taken, or a later checkpoint.
#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
    #define MONAD_VM_FUSED_CHARGE_PURE(REQ)                                    \
        ((gas_remaining -= (REQ).gas, true) &&                                 \
         ::monad::vm::interpreter::stack_holds<(REQ).min_required>(            \
             stack_top, stack_lower_bound) &&                                  \
         ((REQ).max_growth == 0 ||                                             \
          stack_top.next_slot() <                                              \
              MONAD_VM_STACK_LIMIT + (1 - (REQ).max_growth)))
#else
    #define MONAD_VM_FUSED_CHARGE_PURE(REQ) MONAD_VM_FUSED_CHARGE(REQ)
#endif

// Dispatch using OP2, the opcode already read at instr_ptr[1].
// EQ/ISZERO's stack writes prevent GCC from reusing that load itself;
// reusing it explicitly is safe because bytecode is immutable.
#define MONAD_VM_NEXT_OP(OP, OP2) MONAD_VM_NEXT_IMPL(OP, 1, OP2)

#define MONAD_VM_NEXT_PUSH(OP)                                                 \
    MONAD_VM_NEXT_IMPL(OP, ((OP) - PUSH0) + 1, *instr_ptr)

// Dispatch using OP2, the opcode already read just after this PUSH.
// Reuse it across stack writes: bytecode is immutable, but GCC cannot
// rule out aliasing between the stack and the bytecode pointer.
#define MONAD_VM_NEXT_PUSH_OP(OP, OP2)                                         \
    MONAD_VM_NEXT_IMPL(OP, ((OP) - PUSH0) + 1, OP2)

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;
    using enum compiler::EvmOpCode;

    [[gnu::always_inline]] inline bool opcode_at_is(
        uint8_t const *instructions, size_t offset, compiler::EvmOpCode opcode)
    {
        return instructions[offset] == static_cast<uint8_t>(opcode);
    }

#if defined(MONAD_ZKVM_ZISK)
    // Compare N bytecode bytes with a constant pattern using ZisK's DMA
    // comparator (CSR 0x814). The following instruction encodes the length.
    template <size_t N, size_t M>
    [[gnu::always_inline]] inline bool code_matches(
        uint8_t const *const instructions,
        unsigned char const (&pattern)[M]) noexcept
    {
        static_assert(N <= M);
        uint64_t mismatch;
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "addi x0, %2, %5\n\t"
            ".option pop"
            : "=&r"(mismatch)
            : "r"(instructions),
              "r"(pattern),
              "m"(*reinterpret_cast<uint8_t const(*)[N]>(instructions)),
              "m"(pattern),
              "i"(N));
        return mismatch == 0;
    }

#endif

    // Static gas and stack requirements, computed from the opcode table.
    // Track required operands and peak height, not just net stack change.
    struct FusedRequirements
    {
        int64_t gas;
        // Minimum stack height at sequence entry.
        int32_t min_required;
        // Peak growth above the entry height.
        int32_t max_growth;

        bool operator==(FusedRequirements const &) const = default;
    };

    // A non-constexpr call rejects dynamic-gas opcodes at compile time.
    void fused_requirements_rejects_dynamic_gas();

    template <Traits traits, compiler::EvmOpCode... Ops>
    consteval FusedRequirements fused_requirements()
    {
        FusedRequirements requirements{0, 0, 0};
        int32_t height = 0;
        for (auto const op : {Ops...}) {
            auto const info = compiler::opcode_table<traits>[op];
            // Calling a non-constexpr function makes dynamic gas a
            // compile-time error in this static calculation.
            if (info.dynamic_gas) {
                fused_requirements_rejects_dynamic_gas();
            }
            requirements.gas += info.min_gas;
            requirements.min_required =
                // Earlier outputs supply some operands. Subtract the net
                // height change to find the required initial stack height.
                // For PUSH2 JUMPI, PUSH2 supplies one of JUMPI's two inputs.
                std::max(
                    requirements.min_required,
                    static_cast<int32_t>(info.min_stack) - height);
            height = height - static_cast<int32_t>(info.min_stack) +
                     static_cast<int32_t>(info.stack_increase);
            requirements.max_growth = std::max(requirements.max_growth, height);
        }
        return requirements;
    }

#if defined(MONAD_ZKVM_ZISK)
    // Sum base gas, including only the static part of dynamic-cost opcodes.
    // The caller must charge their dynamic cost separately.
    template <Traits traits, compiler::EvmOpCode... Ops>
    consteval int64_t static_gas()
    {
        return (
            static_cast<int64_t>(compiler::opcode_table<traits>[Ops].min_gas) +
            ...);
    }

    // Subtract first, then test the sign. Laundering prevents GCC from
    // replacing this with a comparison that needs another constant load.
    [[gnu::always_inline]] inline bool
    charge_gas(int64_t &gas_remaining, int64_t const gas)
    {
        gas_remaining -= gas;
        MONAD_VM_LAUNDER(gas_remaining);
        return gas_remaining >= 0;
    }

    // Shift in place; the caller guarantees total_shift < 256.
    // Each case fixes the whole-word offset, avoiding dynamic array indexing.
    // Whole-word shifts only copy words; other shifts combine adjacent words.
    [[gnu::always_inline]] inline void
    shr_in_place(uint256_t &value, uint64_t const total_shift) noexcept
    {
        unsigned const intra_word_shift =
            static_cast<unsigned>(total_shift & 63);
        // Used only when intra_word_shift is nonzero, avoiding a shift by 64.
        unsigned const cross_word_shift = 64 - intra_word_shift;
        switch (total_shift >> 6) {
        case 0: {
            if (intra_word_shift == 0) {
                break;
            }
            uint64_t const word0 = value[0], word1 = value[1], word2 = value[2],
                           word3 = value[3];
            value[0] =
                (word0 >> intra_word_shift) | (word1 << cross_word_shift);
            value[1] =
                (word1 >> intra_word_shift) | (word2 << cross_word_shift);
            value[2] =
                (word2 >> intra_word_shift) | (word3 << cross_word_shift);
            value[3] = word3 >> intra_word_shift;
            break;
        }
        case 1: {
            uint64_t const word1 = value[1], word2 = value[2], word3 = value[3];
            if (intra_word_shift == 0) {
                value[0] = word1;
                value[1] = word2;
                value[2] = word3;
            }
            else {
                value[0] =
                    (word1 >> intra_word_shift) | (word2 << cross_word_shift);
                value[1] =
                    (word2 >> intra_word_shift) | (word3 << cross_word_shift);
                value[2] = word3 >> intra_word_shift;
            }
            value[3] = 0;
            break;
        }
        case 2: {
            uint64_t const word2 = value[2], word3 = value[3];
            if (intra_word_shift == 0) {
                value[0] = word2;
                value[1] = word3;
            }
            else {
                value[0] =
                    (word2 >> intra_word_shift) | (word3 << cross_word_shift);
                value[1] = word3 >> intra_word_shift;
            }
            value[2] = 0;
            value[3] = 0;
            break;
        }
        default: {
            uint64_t const word3 = value[3];
            value[0] = word3 >> intra_word_shift;
            value[1] = 0;
            value[2] = 0;
            value[3] = 0;
            break;
        }
        }
    }

    [[gnu::always_inline]] inline void
    shl_in_place(uint256_t &value, uint64_t const total_shift) noexcept
    {
        unsigned const intra_word_shift =
            static_cast<unsigned>(total_shift & 63);
        // Used only when intra_word_shift is nonzero, avoiding a shift by 64.
        unsigned const cross_word_shift = 64 - intra_word_shift;
        switch (total_shift >> 6) {
        case 0: {
            if (intra_word_shift == 0) {
                break;
            }
            uint64_t const word0 = value[0], word1 = value[1], word2 = value[2],
                           word3 = value[3];
            value[3] =
                (word3 << intra_word_shift) | (word2 >> cross_word_shift);
            value[2] =
                (word2 << intra_word_shift) | (word1 >> cross_word_shift);
            value[1] =
                (word1 << intra_word_shift) | (word0 >> cross_word_shift);
            value[0] = word0 << intra_word_shift;
            break;
        }
        case 1: {
            uint64_t const word0 = value[0], word1 = value[1], word2 = value[2];
            if (intra_word_shift == 0) {
                value[3] = word2;
                value[2] = word1;
                value[1] = word0;
            }
            else {
                value[3] =
                    (word2 << intra_word_shift) | (word1 >> cross_word_shift);
                value[2] =
                    (word1 << intra_word_shift) | (word0 >> cross_word_shift);
                value[1] = word0 << intra_word_shift;
            }
            value[0] = 0;
            break;
        }
        case 2: {
            uint64_t const word0 = value[0], word1 = value[1];
            if (intra_word_shift == 0) {
                value[3] = word1;
                value[2] = word0;
            }
            else {
                value[3] =
                    (word1 << intra_word_shift) | (word0 >> cross_word_shift);
                value[2] = word0 << intra_word_shift;
            }
            value[1] = 0;
            value[0] = 0;
            break;
        }
        default: {
            uint64_t const word0 = value[0];
            value[3] = word0 << intra_word_shift;
            value[2] = 0;
            value[1] = 0;
            value[0] = 0;
            break;
        }
        }
    }

    // After validating the destination, charge JUMPDEST's gas and skip it.
    // Invalid jumps must exit before this charge.
    [[gnu::always_inline]] inline uint8_t const *swallow_jumpdest(
        runtime::Context &ctx, uint8_t const *landing, int64_t &gas_remaining)
    {
        gas_remaining -= 1;
        // Hide the previous gas bound to favor a sign test over comparing
        // with -1, which requires loading that constant on RISC-V.
        MONAD_VM_LAUNDER(gas_remaining);
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }
        return landing + 1;
    }

    // Complete <test> PUSH2 JUMPI using the test result directly.
    // Jump to the validated destination encoded at p[2..3], or skip five bytes.
    [[gnu::always_inline]] inline uint8_t const *fused_branch(
        runtime::Context &ctx, uint8_t const *p, bool taken,
        int64_t &gas_remaining)
    {
        // Condition is false; continue after the sequence.
        if (!taken) {
            return p + 5;
        }
        auto const dst = static_cast<size_t>(detail::load_be_k<2>(p + 2));
        if (MONAD_UNLIKELY(!MONAD_VM_CODE_VIEW.is_jumpdest16(dst))) {
            ctx.exit(Error);
        }
        auto const *ip = MONAD_VM_CODE_VIEW.code() + dst;
        ip = swallow_jumpdest(ctx, ip, gas_remaining);
        return ip;
    }
#endif

    template <Traits traits>
    consteval InstrTable make_instruction_table()
    {
        static_assert(traits::evm_rev() >= EvmRevision::Istanbul);

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
            avail(SLOTNUM, slotnum<traits>), // 0x4B,
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

            invalid, // 0xE0,
            invalid, // 0xE1,
            invalid, // 0xE2,
            invalid, // 0xE3,
            invalid, // 0xE4,
            invalid, // 0xE5,
            avail(DUPN, dupn<traits>), // 0xE6,
            avail(SWAPN, swapn<traits>), // 0xE7,
            avail(EXCHANGE, exchange<traits>), // 0xE8,
            invalid, // 0xE9,
            invalid, // 0xEA,
            invalid, // 0xEB,
            invalid, // 0xEC,
            invalid, // 0xED,
            invalid, // 0xEE,
            invalid, // 0xEF,

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
        runtime::Context const &ctx, uint256_t const *stack_lower_bound,
        StackTop const stack_top, uint64_t const base_offset)
    {
        if (!utils::is_fuzzing_monad_vm) {
            return;
        }
        monad::vm::runtime::debug_tstore_stack(
            &ctx,
            stack_top.next_slot(),
            static_cast<uint64_t>(
                stack_top.next_slot() -
                (stack_lower_bound - MONAD_VM_STACK_LOWER_BOUND_BIAS)),
            0,
            base_offset);
    }
#else
    [[gnu::always_inline]] inline void fuzz_tstore_stack(
        runtime::Context const &, uint256_t const *, StackTop, uint64_t const)
    {
        // nop
    }
#endif

    // Arithmetic
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    add(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ADD);
#if defined(MONAD_ZKVM_ZISK)
        // Save a's address before moving to the result slot, so dispatch
        // can reuse the updated stack pointer without an extra register copy.
        ctx.add256_params.a = reinterpret_cast<uint64_t const *>(&*stack_top);
        auto *next = stack_top.next_slot() - 1;
        MONAD_VM_LAUNDER(next);
        stack_top = StackTop{next};
        // Let the precompile handle the 256-bit addition and carries.
        zisk_add256(ctx.add256_params, *stack_top, *stack_top);

        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
#else
        auto &&[a, b] = top_two(stack_top);
        b = a + b;

        MONAD_VM_NEXT(ADD);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MUL, runtime::mul);

        MONAD_VM_NEXT(MUL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SUB);
#if defined(MONAD_ZKVM_ZISK)
        // Save a's address before moving to b. Keep this store ahead of b's
        // loads to avoid extending a's register lifetime.
        ctx.sub256_params.a = reinterpret_cast<uint64_t const *>(&*stack_top);
        asm volatile("" ::: "memory");
        auto *next = stack_top.next_slot() - 1;
        MONAD_VM_LAUNDER(next);
        stack_top = StackTop{next};
        // Compute a - b as a + ~b + 1 modulo 2^256, in place.
        auto &b = *stack_top;
        for (size_t i = 0; i < 4; ++i) {
            b[i] = ~b[i];
        }
        zisk_add256(ctx.sub256_params, b, b);

        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
#else
        auto &&[a, b] = top_two(stack_top);
        b = a - b;

        MONAD_VM_NEXT(SUB);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void udiv(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(DIV, runtime::udiv);

        MONAD_VM_NEXT(DIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SDIV, runtime::sdiv);

        MONAD_VM_NEXT(SDIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MOD, runtime::umod);

        MONAD_VM_NEXT(MOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SMOD, runtime::smod);

        MONAD_VM_NEXT(SMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(ADDMOD, runtime::addmod);

        MONAD_VM_NEXT(ADDMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MULMOD, runtime::mulmod);

        MONAD_VM_NEXT(MULMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(EXP, runtime::exp<traits>);

        MONAD_VM_NEXT(EXP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SIGNEXTEND);
        auto &&[b, x] = top_two(stack_top);
#if defined(MONAD_ZKVM_ZISK)
        // Byte indices 0..7 place the sign bit in the low 64-bit word.
        if ((b[1] | b[2] | b[3]) == 0 && b[0] < 8) {
            unsigned const sign_shift = static_cast<unsigned>(56 - 8 * b[0]);
            // Move the sign bit to bit 63, then shift back arithmetically.
            int64_t const signed_low_word =
                static_cast<int64_t>(x[0] << sign_shift) >> sign_shift;
            // Fill the upper words with zeros or ones according to the sign.
            uint64_t const sign_fill =
                static_cast<uint64_t>(signed_low_word >> 63);
            x[0] = static_cast<uint64_t>(signed_low_word);
            x[1] = sign_fill;
            x[2] = sign_fill;
            x[3] = sign_fill;
            MONAD_VM_NEXT(SIGNEXTEND);
        }
#endif
        signextend_to(b, x);

        MONAD_VM_NEXT(SIGNEXTEND);
    }

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
       uint256_t const *stack_lower_bound, StackTop stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(LT);
#if defined(MONAD_ZKVM_ZISK)
        // Move to the result slot before comparing; dispatch reuses this top.
        auto *next = stack_top.next_slot() - 1;
        MONAD_VM_LAUNDER(next);
        stack_top = StackTop{next};
        *stack_top = *(stack_top + 1) < *stack_top;

        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
#else
        auto &&[a, b] = top_two(stack_top);
        b = a < b;

        MONAD_VM_NEXT(LT);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gt(runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
       uint256_t const *stack_lower_bound, StackTop stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(GT);
#if defined(MONAD_ZKVM_ZISK)
        // As LT.
        auto *next = stack_top.next_slot() - 1;
        MONAD_VM_LAUNDER(next);
        stack_top = StackTop{next};
        *stack_top = *(stack_top + 1) > *stack_top;

        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
#else
        auto &&[a, b] = top_two(stack_top);
        b = a > b;

        MONAD_VM_NEXT(GT);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    slt(runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SLT);
#if defined(MONAD_ZKVM_ZISK)
        // As LT.
        auto *next = stack_top.next_slot() - 1;
        MONAD_VM_LAUNDER(next);
        stack_top = StackTop{next};
        *stack_top = slt(*(stack_top + 1), *stack_top);

        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
#else
        auto &&[a, b] = top_two(stack_top);
        b = slt(a, b);

        MONAD_VM_NEXT(SLT);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sgt(runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SGT);
#if defined(MONAD_ZKVM_ZISK)
        // As LT.
        auto *next = stack_top.next_slot() - 1;
        MONAD_VM_LAUNDER(next);
        stack_top = StackTop{next};
        *stack_top = slt(*stack_top, *(stack_top + 1)); // swapped arguments

        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
#else
        auto &&[a, b] = top_two(stack_top);
        b = slt(b, a); // note swapped arguments

        MONAD_VM_NEXT(SGT);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    eq(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
       uint256_t const *stack_lower_bound, StackTop stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse EQ PUSH2 <dst16> JUMPI. EQ frees a stack slot, so PUSH2
        // cannot overflow once EQ's operands are validated.
        uint8_t const next_opcode = *(instr_ptr + 1);
        if (next_opcode == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            static constexpr auto requirements =
                fused_requirements<traits, EQ, PUSH2, JUMPI>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
                gas_remaining += requirements.gas;
                MONAD_VM_CHECK(EQ);
                // EQ frees a slot, so PUSH2 cannot overflow a valid stack.
                MONAD_DEBUG_ASSERT(
                    (stack_top.next_slot() - 1) -
                        (stack_lower_bound - MONAD_VM_STACK_LOWER_BOUND_BIAS) <
                    static_cast<std::ptrdiff_t>(
                        runtime::EvmStackAllocatorMeta::size));
                MONAD_VM_CHARGE(PUSH2);
                // PUSH2 adds one value, restoring the original stack height.
                MONAD_VM_CHECK_AT(JUMPI, 0);
            }
            // Keep EQ's result in a C++ bool instead of the EVM stack.
            bool const take_jump = (*stack_top == *(stack_top - 1));
            instr_ptr = fused_branch(ctx, instr_ptr, take_jump, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top - 2,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(EQ);
        auto &&[a, b] = top_two(stack_top);
        b = (a == b);

#if defined(MONAD_ZKVM_ZISK)
        MONAD_VM_NEXT_OP(EQ, next_opcode);
#else
        MONAD_VM_NEXT(EQ);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse ISZERO PUSH2 <dst16> JUMPI without storing the test result.
        uint8_t const next_opcode = *(instr_ptr + 1);
        if (next_opcode == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            static constexpr auto requirements =
                fused_requirements<traits, ISZERO, PUSH2, JUMPI>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
                gas_remaining += requirements.gas;
                MONAD_VM_CHECK(ISZERO);
                MONAD_VM_CHECK_AT(PUSH2, 0);
                MONAD_VM_CHECK_AT(JUMPI, 1);
            }
            bool const take_jump = !*stack_top;
            instr_ptr = fused_branch(ctx, instr_ptr, take_jump, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top - 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(ISZERO);
        auto &a = *stack_top;
        a = !a;

#if defined(MONAD_ZKVM_ZISK)
        MONAD_VM_NEXT_OP(ISZERO, next_opcode);
#else
        MONAD_VM_NEXT(ISZERO);
#endif
    }

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(AND);
        auto &&[a, b] = top_two(stack_top);
        b = a & b;

        MONAD_VM_NEXT(AND);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    or_(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(OR);
        auto &&[a, b] = top_two(stack_top);
        b = a | b;

        MONAD_VM_NEXT(OR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void xor_(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(XOR);
        auto &&[a, b] = top_two(stack_top);
        b = a ^ b;

        MONAD_VM_NEXT(XOR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void not_(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(NOT);
        auto &a = *stack_top;
        a = ~a;

        MONAD_VM_NEXT(NOT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void byte(
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(BYTE);
        auto &&[i, x] = top_two(stack_top);
        x = byte(i, x);

        MONAD_VM_NEXT(BYTE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shl(runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SHL);
        auto &&[shift, value] = top_two(stack_top);
#if defined(MONAD_ZKVM_ZISK)
        if ((shift[1] | shift[2] | shift[3]) == 0 && shift[0] < 256) {
            shl_in_place(value, shift[0]);
        }
        else {
            value = uint256_t{};
        }
#else
        value <<= shift;
#endif

        MONAD_VM_NEXT(SHL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shr(runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SHR);
        auto &&[shift, value] = top_two(stack_top);
#if defined(MONAD_ZKVM_ZISK)
        if ((shift[1] | shift[2] | shift[3]) == 0 && shift[0] < 256) {
            shr_in_place(value, shift[0]);
        }
        else {
            value = uint256_t{};
        }
#else
        value >>= shift;
#endif

        MONAD_VM_NEXT(SHR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sar(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SAR);
        auto &&[shift, value] = top_two(stack_top);
        value = sar(shift, value);

        MONAD_VM_NEXT(SAR);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    clz(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SHA3, runtime::sha3<traits>);

        MONAD_VM_NEXT(SHA3);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ADDRESS);
        push(stack_top, runtime::uint256_from_address(ctx.env.recipient));

        MONAD_VM_NEXT(ADDRESS);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BALANCE, runtime::balance<traits>);

        MONAD_VM_NEXT(BALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CALLER);
        push(stack_top, runtime::uint256_from_address(ctx.env.sender));

        MONAD_VM_NEXT(CALLER);
    }

#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
    // Test whether the call transfers zero wei; byte order does not matter.
    [[gnu::always_inline]] inline bool
    call_value_is_zero(runtime::Context const &ctx) noexcept
    {
        // Separate 8-byte reads avoid staging a 32-byte DMA copy on the stack.
        unsigned char const *const value_bytes = ctx.env.value.bytes;
        uint64_t value_word_0, value_word_1, value_word_2, value_word_3;
        __builtin_memcpy(&value_word_0, value_bytes, 8);
        __builtin_memcpy(&value_word_1, value_bytes + 8, 8);
        __builtin_memcpy(&value_word_2, value_bytes + 16, 8);
        __builtin_memcpy(&value_word_3, value_bytes + 24, 8);
        return (value_word_0 | value_word_1 | value_word_2 | value_word_3) == 0;
    }

    // Recognize a via-IR ABI check with a non-taken error branch:
    //   PUSH0 (or PUSH1 <minimum>) CALLDATASIZE PUSH1 3 NOT ADD SLT
    //   PUSH2 <revert> JUMPI
    // Return its bytecode length when enough argument bytes follow the
    // 4-byte selector; otherwise return zero. Needs three temporary slots.
    template <Traits traits>
    [[gnu::always_inline]] inline size_t ir_bound_length(
        runtime::Context const &ctx, uint8_t const *const bound_code) noexcept
    {
        bool const push0 = bound_code[0] == static_cast<std::uint8_t>(PUSH0);
        if (push0 && traits::evm_rev() < EvmRevision::Shanghai) {
            return 0;
        }
        if (!push0 && bound_code[0] != static_cast<std::uint8_t>(PUSH1)) {
            return 0;
        }
        size_t const minimum_argument_bytes = push0 ? 0 : bound_code[1];
        auto const *const check_code = bound_code + (push0 ? 1 : 2);
        if (!(check_code[0] == static_cast<std::uint8_t>(CALLDATASIZE) &&
              check_code[1] == static_cast<std::uint8_t>(PUSH1) &&
              check_code[2] == 3 &&
              check_code[3] == static_cast<std::uint8_t>(NOT) &&
              check_code[4] == static_cast<std::uint8_t>(ADD) &&
              check_code[5] == static_cast<std::uint8_t>(SLT) &&
              check_code[6] == static_cast<std::uint8_t>(PUSH2) &&
              check_code[9] == static_cast<std::uint8_t>(JUMPI))) {
            return 0;
        }
        uint64_t const calldata_size = ctx.env.input_data_size;
        if (calldata_size < 4 || calldata_size - 4 < minimum_argument_bytes) {
            return 0;
        }
        return static_cast<size_t>(check_code - bound_code) + 10;
    }

    // Fixed bytes from JUMPI through POP, excluding the jump destination.
    alignas(8) inline constexpr unsigned char nonpayable_push0_tail[8] = {
        static_cast<unsigned char>(JUMPI),
        static_cast<unsigned char>(PUSH0),
        static_cast<unsigned char>(DUP1),
        static_cast<unsigned char>(REVERT),
        static_cast<unsigned char>(JUMPDEST),
        static_cast<unsigned char>(POP)};
    alignas(8) inline constexpr unsigned char nonpayable_push1_tail[8] = {
        static_cast<unsigned char>(JUMPI),
        static_cast<unsigned char>(PUSH1),
        0,
        static_cast<unsigned char>(DUP1),
        static_cast<unsigned char>(REVERT),
        static_cast<unsigned char>(JUMPDEST),
        static_cast<unsigned char>(POP)};

    // Legacy Solidity's non-payable check:
    //   CALLVALUE DUP1 ISZERO PUSH2 <ok> JUMPI PUSH1 0 DUP1 REVERT
    //   ok: JUMPDEST POP                     (or PUSH0 DUP1 REVERT)
    // With zero value, jump over REVERT and remove the temporary CALLVALUE.
    // Unsupported patterns use ordinary dispatch.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void callvalue_nonpayable(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const *const instructions = instr_ptr;
        // PUSH0 occupies one byte less than PUSH1 0, shifting the success
        // label.
        size_t success_offset;
        bool matches_revert_tail;
        if (opcode_at_is(instructions, 7, PUSH0)) {
            success_offset = 10;
            matches_revert_tail =
                code_matches<6>(instructions + 6, nonpayable_push0_tail);
        }
        else {
            success_offset = 11;
            matches_revert_tail =
                code_matches<7>(instructions + 6, nonpayable_push1_tail);
        }
        size_t const jump_destination = detail::load_be_k<2>(instructions + 4);
        size_t const callvalue_offset =
            static_cast<size_t>(instructions - MONAD_VM_CODE_VIEW.code());
        // The full pattern proves this destination is a JUMPDEST instruction,
        // so no bitmap lookup is needed.
        if (MONAD_UNLIKELY(!(
                matches_revert_tail && opcode_at_is(instructions, 2, ISZERO) &&
                opcode_at_is(instructions, 3, PUSH2) &&
                jump_destination == callvalue_offset + success_offset &&
                stack_top.next_slot() <= MONAD_VM_STACK_LIMIT - 3 &&
                call_value_is_zero(ctx)))) {
            // Execute CALLVALUE directly to avoid re-entering this helper.
            MONAD_VM_CHECK(CALLVALUE);
            push(stack_top, load_be<uint256_t>(ctx.env.value));
            MONAD_VM_NEXT(CALLVALUE);
        }
        // Charge through POP before checking gas: this path has no side
        // effects.
        gas_remaining -= static_gas<
            traits,
            CALLVALUE,
            DUP1,
            ISZERO,
            PUSH2,
            JUMPI,
            JUMPDEST,
            POP>();
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        MONAD_VM_FUSED_NEXT(success_offset + 2, 0);
    }

    // Fuse CALLVALUE PUSH2 <revert> JUMPI when the call transfers zero wei.
    // Also skip a recognized ABI length check when enough arguments exist.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void callvalue_ir(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const *const instructions = instr_ptr;
        if (MONAD_UNLIKELY(
                !(instructions[4] == static_cast<std::uint8_t>(JUMPI) &&
                  stack_top.next_slot() <= MONAD_VM_STACK_LIMIT - 3 &&
                  call_value_is_zero(ctx)))) {
            // Execute CALLVALUE directly to avoid re-entering this helper.
            MONAD_VM_CHECK(CALLVALUE);
            push(stack_top, load_be<uint256_t>(ctx.env.value));
            MONAD_VM_NEXT(CALLVALUE);
        }
        // These pure instructions defer the gas check to the next checkpoint.
        gas_remaining -= static_gas<traits, CALLVALUE, PUSH2, JUMPI>();
        size_t const calldata_check_bytecode_length =
            ir_bound_length<traits>(ctx, instructions + 5);
        if (calldata_check_bytecode_length != 0) {
            gas_remaining -= instructions[5] == static_cast<std::uint8_t>(PUSH0)
                                 ? static_gas<
                                       traits,
                                       PUSH0,
                                       CALLDATASIZE,
                                       PUSH1,
                                       NOT,
                                       ADD,
                                       SLT,
                                       PUSH2,
                                       JUMPI>()
                                 : static_gas<
                                       traits,
                                       PUSH1,
                                       CALLDATASIZE,
                                       PUSH1,
                                       NOT,
                                       ADD,
                                       SLT,
                                       PUSH2,
                                       JUMPI>();
        }
        instr_ptr += 5 + calldata_check_bytecode_length;
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }
#endif

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        // Solidity reads the call's value for its non-payable test, each
        // generator's in a twin: DUP1 follows in the legacy one, PUSH2 in
        // the via-IR one.
        if (instr_ptr[1] == static_cast<std::uint8_t>(DUP1)) {
            MONAD_VM_MUST_TAIL return callvalue_nonpayable<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        if (instr_ptr[1] == static_cast<std::uint8_t>(PUSH2)) {
            MONAD_VM_MUST_TAIL return callvalue_ir<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(CALLVALUE);
        push(stack_top, load_be<uint256_t>(ctx.env.value));

        MONAD_VM_NEXT(CALLVALUE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECKED_RUNTIME_CALL(CALLDATALOAD, runtime::calldataload);

        MONAD_VM_NEXT(CALLDATALOAD);
    }

#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
    // Aligned storage for the three selector-extraction patterns. Only the
    // first 5, 6 or 41 bytes are compared; trailing padding is ignored.
    alignas(8) inline constexpr unsigned char selector_push0_pattern[8] = {
        static_cast<unsigned char>(PUSH0),
        static_cast<unsigned char>(CALLDATALOAD),
        static_cast<unsigned char>(PUSH1),
        0xe0,
        static_cast<unsigned char>(SHR)};
    alignas(8) inline constexpr unsigned char selector_push1_pattern[8] = {
        static_cast<unsigned char>(PUSH1),
        0,
        static_cast<unsigned char>(CALLDATALOAD),
        static_cast<unsigned char>(PUSH1),
        0xe0,
        static_cast<unsigned char>(SHR)};
    alignas(8) inline constexpr unsigned char selector_div_pattern[48] = {
        static_cast<unsigned char>(PUSH1),
        0,
        static_cast<unsigned char>(CALLDATALOAD),
        static_cast<unsigned char>(PUSH29),
        1,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        static_cast<unsigned char>(SWAP1),
        static_cast<unsigned char>(DIV),
        static_cast<unsigned char>(PUSH4),
        0xff,
        0xff,
        0xff,
        0xff,
        static_cast<unsigned char>(AND)};

    // These fusions use deferred gas checks; eager mode keeps per-opcode
    // dispatch. Recognize one of these selector extractions:
    //
    //     PUSH1 0 CALLDATALOAD PUSH1 0xe0 SHR
    //     PUSH0 CALLDATALOAD PUSH1 0xe0 SHR
    //     PUSH1 0 CALLDATALOAD PUSH29 1 << 224 SWAP1 DIV PUSH4 0xffffffff AND
    //
    // Charge its gas, push the first four calldata bytes and return the
    // bytecode length. Return zero without changes for an unknown pattern.
    // The caller guarantees four calldata bytes and room for two stack slots.
    template <Traits traits>
    [[gnu::always_inline]] inline size_t push_selector(
        runtime::Context const &ctx, uint8_t const *const extraction_code,
        StackTop const stack_top, int64_t &gas_remaining)
    {
        size_t extraction_length = 0;
        if (traits::evm_rev() >= EvmRevision::Shanghai &&
            opcode_at_is(extraction_code, 0, PUSH0)) {
            if (code_matches<5>(extraction_code, selector_push0_pattern)) {
                gas_remaining -=
                    static_gas<traits, PUSH0, CALLDATALOAD, PUSH1, SHR>();
                extraction_length = 5;
            }
        }
        else if (opcode_at_is(extraction_code, 0, PUSH1)) {
            if (code_matches<6>(extraction_code, selector_push1_pattern)) {
                gas_remaining -=
                    static_gas<traits, PUSH1, CALLDATALOAD, PUSH1, SHR>();
                extraction_length = 6;
            }
            // Offset 33 is safe with the code's 33-byte zero padding. A
            // nonzero SWAP1 there guarantees enough real code for the 41-byte
            // comparison to remain within the padded allocation.
            else if (
                opcode_at_is(extraction_code, 33, SWAP1) &&
                code_matches<41>(extraction_code, selector_div_pattern)) {
                gas_remaining -= static_gas<
                    traits,
                    PUSH1,
                    CALLDATALOAD,
                    PUSH29,
                    SWAP1,
                    DIV,
                    PUSH4,
                    AND>();
                extraction_length = 41;
            }
        }
        if (extraction_length != 0) {
            stack_top[1] = uint256_t{detail::load_be_k<4>(ctx.env.input_data)};
        }
        return extraction_length;
    }

    // Fuse the calldata-size check with an optional selector extraction:
    //
    //     CALLDATASIZE LT PUSH2 <fallback> JUMPI          (not taken)
    //     CALLDATASIZE LT ISZERO PUSH2 <dispatch> JUMPI   (taken)
    //
    // Requires 4 on the stack and at least four calldata bytes. Consume the
    // 4, then extract the selector if the following code matches a known form.
    // Otherwise execute CALLDATASIZE here and resume ordinary dispatch.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void calldata_selector(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const *const instructions = instr_ptr;
        bool const falls_through = opcode_at_is(instructions, 2, PUSH2) &&
                                   opcode_at_is(instructions, 5, JUMPI);
        bool const jumps_to_dispatch = opcode_at_is(instructions, 2, ISZERO) &&
                                       opcode_at_is(instructions, 3, PUSH2) &&
                                       opcode_at_is(instructions, 6, JUMPI);
        if (MONAD_UNLIKELY(!(
                (falls_through || jumps_to_dispatch) &&
                ctx.env.input_data_size >= 4 &&
                stack_holds<1>(stack_top, stack_lower_bound) &&
                stack_top.next_slot() < MONAD_VM_STACK_LIMIT &&
                stack_top[0][0] == 4 &&
                (stack_top[0][1] | stack_top[0][2] | stack_top[0][3]) == 0))) {
            // Execute CALLDATASIZE directly to avoid re-entering this helper.
            MONAD_VM_CHECK(CALLDATASIZE);
            push(stack_top, ctx.env.input_data_size);
            MONAD_VM_NEXT(CALLDATASIZE);
        }
        // A taken jump checks gas at JUMPDEST; otherwise the next checkpoint
        // does.
        uint8_t const *extraction_code;
        if (falls_through) {
            gas_remaining -=
                static_gas<traits, CALLDATASIZE, LT, PUSH2, JUMPI>();
            extraction_code = instructions + 6;
        }
        else {
            gas_remaining -=
                static_gas<traits, CALLDATASIZE, LT, ISZERO, PUSH2, JUMPI>();
            extraction_code =
                fused_branch(ctx, instructions + 2, true, gas_remaining);
        }
        size_t const extraction_length = push_selector<traits>(
            ctx, extraction_code, stack_top - 1, gas_remaining);
        instr_ptr = extraction_code + extraction_length;
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top - (extraction_length == 0 ? 1 : 0),
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // Fuse the ABI decoder's remaining-length check:
    //
    //     CALLDATASIZE SUB PUSH1 <minimum> DUP2 LT ISZERO PUSH2 <decode> JUMPI
    //
    // Replace the top offset with calldata_size - offset, then jump if enough
    // bytes remain. Unsupported patterns and subtraction underflow fall back.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void calldata_bound(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const *const instructions = instr_ptr;
        uint64_t const calldata_size = ctx.env.input_data_size;
        if (MONAD_UNLIKELY(
                !(opcode_at_is(instructions, 2, PUSH1) &&
                  opcode_at_is(instructions, 4, DUP2) &&
                  opcode_at_is(instructions, 5, LT) &&
                  opcode_at_is(instructions, 6, ISZERO) &&
                  opcode_at_is(instructions, 7, PUSH2) &&
                  opcode_at_is(instructions, 10, JUMPI) &&
                  stack_holds<1>(stack_top, stack_lower_bound) &&
                  stack_top.next_slot() < MONAD_VM_STACK_LIMIT - 1 &&
                  (stack_top[0][1] | stack_top[0][2] | stack_top[0][3]) == 0 &&
                  stack_top[0][0] <= calldata_size))) {
            // Execute CALLDATASIZE directly to avoid re-entering this helper.
            MONAD_VM_CHECK(CALLDATASIZE);
            push(stack_top, ctx.env.input_data_size);
            MONAD_VM_NEXT(CALLDATASIZE);
        }
        // A taken jump checks gas at JUMPDEST; otherwise the next checkpoint
        // does.
        gas_remaining -= static_gas<
            traits,
            CALLDATASIZE,
            SUB,
            PUSH1,
            DUP2,
            LT,
            ISZERO,
            PUSH2,
            JUMPI>();
        uint256_t &calldata_offset = stack_top[0];
        uint64_t const remaining_bytes = calldata_size - calldata_offset[0];
        calldata_offset = uint256_t{remaining_bytes};
        instr_ptr = fused_branch(
            ctx,
            instructions + 6,
            remaining_bytes >= instructions[3],
            gas_remaining);
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }
#endif

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        // Solidity reads the calldata's size for two idioms, each with a
        // twin: the dispatch prologue (LT follows) and the ABI decoder's
        // bound (SUB follows).
        if (instr_ptr[1] == static_cast<std::uint8_t>(LT)) {
            MONAD_VM_MUST_TAIL return calldata_selector<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        if (instr_ptr[1] == static_cast<std::uint8_t>(SUB)) {
            MONAD_VM_MUST_TAIL return calldata_bound<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(CALLDATASIZE);
        push(stack_top, ctx.env.input_data_size);

        MONAD_VM_NEXT(CALLDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CALLDATACOPY, runtime::calldatacopy<traits>);

        MONAD_VM_NEXT(CALLDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CODESIZE);
        push(stack_top, ctx.env.code_size);

        MONAD_VM_NEXT(CODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CODECOPY, runtime::codecopy<traits>);

        MONAD_VM_NEXT(CODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GASPRICE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->tx_gas_price));

        MONAD_VM_NEXT(GASPRICE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODESIZE, runtime::extcodesize<traits>);

        MONAD_VM_NEXT(EXTCODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODECOPY, runtime::extcodecopy<traits>);

        MONAD_VM_NEXT(EXTCODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(RETURNDATASIZE);
        push(stack_top, ctx.env.return_data_size);

        MONAD_VM_NEXT(RETURNDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            RETURNDATACOPY, runtime::returndatacopy<traits>);

        MONAD_VM_NEXT(RETURNDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODEHASH, runtime::extcodehash<traits>);

        MONAD_VM_NEXT(EXTCODEHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BLOCKHASH, runtime::blockhash);

        MONAD_VM_NEXT(BLOCKHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(TIMESTAMP);
        push(stack_top, ctx.env.tx_context->block_timestamp);

        MONAD_VM_NEXT(TIMESTAMP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(NUMBER);
        push(stack_top, ctx.env.tx_context->block_number);

        MONAD_VM_NEXT(NUMBER);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GASLIMIT);
        push(stack_top, ctx.env.tx_context->block_gas_limit);

        MONAD_VM_NEXT(GASLIMIT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CHAINID);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->chain_id));

        MONAD_VM_NEXT(CHAINID);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SELFBALANCE, runtime::selfbalance);

        MONAD_VM_NEXT(SELFBALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BASEFEE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->block_base_fee));

        MONAD_VM_NEXT(BASEFEE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BLOBHASH, runtime::blobhash);

        MONAD_VM_NEXT(BLOBHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BLOBBASEFEE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->blob_base_fee));

        MONAD_VM_NEXT(BLOBBASEFEE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void slotnum(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        check_requirements<SLOTNUM, traits>(
            ctx,
            MONAD_VM_CODE_VIEW,
            stack_lower_bound,
            stack_top,
            gas_remaining);
        push(stack_top, ctx.env.tx_context->block_round);

        MONAD_VM_NEXT(SLOTNUM);
    }

    // Memory & Storage

    // Isolate rare memory growth to avoid register spills on MLOAD's fast path.
    // Continue dispatch here instead of returning to mload. Gas and stack
    // checks have already run; do not repeat them.
    template <Traits traits>
    [[gnu::noinline, gnu::cold]] MONAD_VM_TWIN_CALL void mload_grow(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        call_runtime(runtime::mload<traits>, ctx, stack_top, gas_remaining);

        MONAD_VM_NEXT(MLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK_OWN_GAS(MLOAD);

        ctx.gas_remaining = gas_remaining;
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mload_grow<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        runtime::mload_at<traits>(&ctx, &*stack_top, offset);
        gas_remaining = ctx.gas_remaining;

        MONAD_VM_NEXT(MLOAD);
    }

    // Use the generic path for allocation or a memory-limit failure.
    // It receives the gas remaining before any expansion charge.
    template <Traits traits>
    [[gnu::noinline, gnu::cold]] MONAD_VM_TWIN_CALL void mstore_slow(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        call_runtime(runtime::mstore<traits>, ctx, stack_top, gas_remaining);

        MONAD_VM_NEXT(MSTORE);
    }

    // Expand within the allocated capacity and charge the local gas counter.
    // Tail calls keep allocation off this path.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void mstore_grow(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        // mstore validated the offset, so its low word is all of it.
        auto const offset = runtime::Memory::Offset::unsafe_from(
            static_cast<runtime::Memory::Offset::rep>((*stack_top)[0]));
        auto const word_count = runtime::Context::memory_size_to_word_count(
            offset + runtime::bin<32>);
        auto const new_size =
            runtime::Context::word_count_to_memory_size(word_count);
        if (MONAD_UNLIKELY(
                ctx.memory.capacity < *new_size ||
                !ctx.is_memory_size_in_bound<traits>(new_size))) {
            MONAD_VM_MUST_TAIL return mstore_slow<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        auto const new_cost =
            runtime::Context::memory_cost_from_word_count<traits>(word_count);
        gas_remaining -= new_cost - ctx.memory.cost;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        ctx.memory.size = *new_size;
        ctx.memory.cost = new_cost;
        runtime::mstore_at<traits>(&ctx, offset, &stack_top[-1]);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        // Encourage pointer-register reuse instead of save/restore copies.
        auto *top = stack_top.next_slot();
        MONAD_VM_LAUNDER(top);
        stack_top = StackTop{top};
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_CHECK_OWN_GAS(MSTORE);

        // The base gas is already charged. In-bounds stores need no expansion
        // charge or gas synchronization.
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        runtime::mstore_at<traits>(&ctx, offset, &stack_top[-1]);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MSTORE8, runtime::mstore8<traits>);

        MONAD_VM_NEXT(MSTORE8);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MCOPY, runtime::mcopy<traits>);

        MONAD_VM_NEXT(MCOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SSTORE, runtime::sstore<traits>);

        MONAD_VM_NEXT(SSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SLOAD, runtime::sload<traits>);

        MONAD_VM_NEXT(SLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(TSTORE, runtime::tstore);

        MONAD_VM_NEXT(TSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(TLOAD, runtime::tload);

        MONAD_VM_NEXT(TLOAD);
    }

    // Execution Intercode
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
       uint256_t const *stack_lower_bound, StackTop stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(PC);
        push(stack_top, instr_ptr - MONAD_VM_CODE_VIEW.code());

        MONAD_VM_NEXT(PC);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(MSIZE);
        push(stack_top, ctx.memory.size);

        MONAD_VM_NEXT(MSIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GAS);
        push(stack_top, gas_remaining);

        MONAD_VM_NEXT(GAS);
    }

    // Stack

    // Isolate SHR/SAR register pressure to keep push<1> frame-free.
    // Gas and stack are already checked; instr_ptr still points to PUSH1.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_shr(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        *stack_top >>= uint256_t{*(instr_ptr + 1)};
        MONAD_VM_FUSED_NEXT(3, 0);
    }

    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_sar(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        *stack_top = sar(uint256_t{*(instr_ptr + 1)}, *stack_top);
        MONAD_VM_FUSED_NEXT(3, 0);
    }

#if defined(MONAD_ZKVM_ZISK)
    // The first two PUSH1s reserve slots for [1, 1] without writing them.
    // Finish 2^k - 1 without reading either slot.
    // instr_ptr points at the remaining sequence:
    //   offset:  0      1    2    3    4 (optional)
    //            PUSH1  [k] SHL  SUB  AND
    // Without AND: [..., unused, unused] -> [..., mask].
    // With AND:    [..., x, unused, unused] -> [..., x & mask].
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_mask(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const mask_bits = static_cast<size_t>(*(instr_ptr + 1));
        // k / 64 selects the boundary word; its low k % 64 bits are ones.
        // Lower words are all ones, and higher words are zero.
        size_t const boundary_word = mask_bits >> 6;
        uint64_t const boundary_mask = (uint64_t{1} << (mask_bits & 63)) - 1;
        if (*(instr_ptr + 4) == static_cast<std::uint8_t>(AND)) {
            // Apply the mask directly to x, below the two reserved slots.
            static constexpr auto requirements =
                fused_requirements<traits, PUSH1, SHL, SUB, AND>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
                gas_remaining += requirements.gas;
                MONAD_VM_CHECK(PUSH1);
                MONAD_VM_CHECK_AT(SHL, 1);
                MONAD_VM_CHECK_AT(SUB, 0);
                MONAD_VM_CHECK_AT(AND, -1);
            }
            auto &value = *(stack_top - 2);
            if (boundary_word == 2) {
                value[2] &= boundary_mask;
                value[3] = 0;
            }
            else if (boundary_word == 1) {
                value[1] &= boundary_mask;
                value[2] = 0;
                value[3] = 0;
            }
            else if (boundary_word == 3) {
                value[3] &= boundary_mask;
            }
            else {
                value[0] &= boundary_mask;
                value[1] = 0;
                value[2] = 0;
                value[3] = 0;
            }
            MONAD_VM_FUSED_NEXT(5, -2);
        }
        static constexpr auto requirements =
            fused_requirements<traits, PUSH1, SHL, SUB>();
        if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
            gas_remaining += requirements.gas;
            MONAD_VM_CHECK(PUSH1);
            MONAD_VM_CHECK_AT(SHL, 1);
            MONAD_VM_CHECK_AT(SUB, 0);
        }
        auto &mask = *(stack_top - 1);
        uint64_t const all_ones = ~uint64_t{0};
        if (boundary_word == 2) {
            mask[0] = all_ones;
            mask[1] = all_ones;
            mask[2] = boundary_mask;
            mask[3] = 0;
        }
        else if (boundary_word == 1) {
            mask[0] = all_ones;
            mask[1] = boundary_mask;
            mask[2] = 0;
            mask[3] = 0;
        }
        else if (boundary_word == 3) {
            mask[0] = all_ones;
            mask[1] = all_ones;
            mask[2] = all_ones;
            mask[3] = boundary_mask;
        }
        else {
            mask[0] = boundary_mask;
            mask[1] = 0;
            mask[2] = 0;
            mask[3] = 0;
        }
        MONAD_VM_FUSED_NEXT(4, -1);
    }

    // OP is the opcode AFTER PUSH1: PUSH1 7 ADD selects push1_then<ADD>,
    // while PUSH1 7 PUSH1 9 selects push1_then<PUSH1>.
    // instr_ptr still points to the first PUSH1, which has not executed yet.
    // Slot dispatch already checked room for its temporary stack entry.
    // Slot wrappers also provide the normal handler for a direct fallback.
    template <uint8_t OP, Traits traits, InstrEval fallback_handler = nullptr>
    MONAD_VM_INSTRUCTION_CALL void push1_then(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        if constexpr (OP == PUSH1 && has_slots<traits>) {
            // [PUSH1][a][PUSH1][b][OP]: push a, then enter OP's prefix with
            // instr_ptr on the second PUSH1. This lets PUSH1 b fuse with OP.
            // Without slots, keep the two-push path below: no prefix exists.
            // Preserve the special two-ones path for push1_mask first.
            uint8_t const first_immediate = *(instr_ptr + 1);
            if (MONAD_UNLIKELY(
                    first_immediate == 1 && *(instr_ptr + 3) == 1 &&
                    *(instr_ptr + 4) == static_cast<std::uint8_t>(PUSH1) &&
                    *(instr_ptr + 6) == static_cast<std::uint8_t>(SHL) &&
                    *(instr_ptr + 7) == static_cast<std::uint8_t>(SUB))) {
                static constexpr auto pair_requirements =
                    fused_requirements<traits, PUSH1, PUSH1>();
                if (MONAD_UNLIKELY(
                        !MONAD_VM_FUSED_CHARGE_PURE(pair_requirements))) {
                    gas_remaining += pair_requirements.gas;
                    MONAD_VM_CHECK(PUSH1);
                    MONAD_VM_CHECK_AT(PUSH1, 1);
                }
                // Skip pushing the two constant ones: push1_mask never reads
                // them. Still advance stack_top by two and preserve their
                // gas and stack checks.
                instr_ptr += 4;
                MONAD_VM_MUST_TAIL return push1_mask<traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top + 2,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
            interpreter::push(stack_top, uint256_t{first_immediate});
            gas_remaining -= static_gas<traits, PUSH1>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
            // Re-entering a prefix bypasses push<1>'s check for the second
            // PUSH1.
            if (MONAD_UNLIKELY((gas_remaining < static_gas<traits, PUSH1>()))) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
    #endif
            if (MONAD_UNLIKELY(
                    stack_top.next_slot() + 1 >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            MONAD_VM_PUSH1_PREFIX_DISPATCH(
                *(instr_ptr + 4), stack_top + 1, gas_remaining, instr_ptr + 2);
        }
        else if constexpr (OP == PUSH1) {
            // Fuse PUSH1 <a> PUSH1 <b>, saving one dispatch.
            // The pair needs two free slots and 6 gas; the fallback preserves
            // per-opcode checks and error order.
            // Zero padding supplies a missing second immediate.
            static constexpr auto pair_requirements =
                fused_requirements<traits, PUSH1, PUSH1>();
            if (MONAD_UNLIKELY(
                    !MONAD_VM_FUSED_CHARGE_PURE(pair_requirements))) {
                gas_remaining += pair_requirements.gas;
                MONAD_VM_CHECK(PUSH1);
                MONAD_VM_CHECK_AT(PUSH1, 1);
            }
            // Read both immediates before storing, so instr_ptr is no
            // longer needed for these loads when dispatch advances it.
            uint8_t const first_immediate = *(instr_ptr + 1);
            uint8_t const second_immediate = *(instr_ptr + 3);
            interpreter::push(stack_top, uint256_t{first_immediate});
            interpreter::push(stack_top + 1, uint256_t{second_immediate});
            // Continue in push1_mask when the two ones start a mask
            // pattern. Select the tail-call target here to avoid a separate
            // call.
            instr_ptr += 4;
            MONAD_VM_LAUNDER(instr_ptr);
            bool const starts_mask =
                first_immediate == 1 && second_immediate == 1 &&
                *instr_ptr == static_cast<std::uint8_t>(PUSH1) &&
                *(instr_ptr + 2) == static_cast<std::uint8_t>(SHL) &&
                *(instr_ptr + 3) == static_cast<std::uint8_t>(SUB);
            auto const next_handler = starts_mask
                                          ? &push1_mask<traits>
                                          : MONAD_VM_TABLE_REF[*instr_ptr];
            MONAD_VM_MUST_TAIL return next_handler(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top + 2,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == MLOAD || OP == MSTORE) {
            // [PUSH1][offset][MLOAD/MSTORE]: read the byte offset directly,
            // without pushing and rereading a 256-bit address. It is <= 255.
            // MLOAD pushes the loaded value; MSTORE consumes the existing top.
            // Fuse only when all 32 bytes are already in EVM memory.
            // Charge both opcodes; eager mode also checks gas before access.
            auto const memory_offset = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(*(instr_ptr + 1)));
            if constexpr (OP == MLOAD) {
                if (MONAD_LIKELY(ctx.memory.size >= *memory_offset + 32)) {
                    gas_remaining -= static_gas<traits, PUSH1, MLOAD>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
                    if (MONAD_UNLIKELY(gas_remaining < 0)) {
                        MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
                    }
    #endif
                    runtime::mload_at<traits>(
                        &ctx, stack_top.next_slot(), memory_offset);
                    MONAD_VM_FUSED_NEXT(3, 1);
                }
            }
            else {
                // PUSH1 supplies the offset; the value to store is already on
                // top.
                if (MONAD_LIKELY(
                        stack_holds<1>(stack_top, stack_lower_bound) &&
                        ctx.memory.size >= *memory_offset + 32)) {
                    gas_remaining -= static_gas<traits, PUSH1, MSTORE>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
                    if (MONAD_UNLIKELY(gas_remaining < 0)) {
                        MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
                    }
    #endif
                    runtime::mstore_at<traits>(
                        &ctx, memory_offset, &*stack_top);
                    MONAD_VM_FUSED_NEXT(3, -1);
                }
            }
            // Materialize PUSH1 and let the ordinary handler check operands
            // and charge for memory expansion when needed.
            interpreter::push(stack_top, uint256_t{*(instr_ptr + 1)});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == NOT) {
            // Push the complement directly, without first pushing the
            // immediate.
            gas_remaining -= static_gas<traits, PUSH1, NOT>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
            if (MONAD_UNLIKELY(gas_remaining < 0)) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
    #endif
            interpreter::push(stack_top, ~uint256_t{*(instr_ptr + 1)});
            MONAD_VM_FUSED_NEXT(3, 1);
        }
        else if constexpr (OP == CALLDATALOAD) {
            // Read at the immediate byte offset. A short read is padded with
            // zeros; an offset past the calldata returns zero.
            gas_remaining -= static_gas<traits, PUSH1, CALLDATALOAD>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
            if (MONAD_UNLIKELY(gas_remaining < 0)) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
    #endif
            uint8_t const immediate = *(instr_ptr + 1);
            auto const available_bytes =
                static_cast<int64_t>(ctx.env.input_data_size) -
                int64_t{immediate};
            auto &result = *stack_top.next_slot();
            if (MONAD_LIKELY(available_bytes >= 32)) {
                auto const *const input = ctx.env.input_data + immediate;
                result[3] = load_be_unsafe<uint64_t>(input);
                result[2] = load_be_unsafe<uint64_t>(input + 8);
                result[1] = load_be_unsafe<uint64_t>(input + 16);
                result[0] = load_be_unsafe<uint64_t>(input + 24);
            }
            else if (available_bytes > 0) {
                result = runtime::uint256_load_bounded_be(
                    ctx.env.input_data + immediate, available_bytes);
            }
            else {
                result = 0;
            }
            MONAD_VM_FUSED_NEXT(3, 1);
        }
        else if constexpr (OP == AND) {
            // Mask the existing top with the immediate byte.
            uint8_t const immediate = *(instr_ptr + 1);
            if (MONAD_LIKELY(stack_holds<1>(stack_top, stack_lower_bound))) {
                gas_remaining -= static_gas<traits, PUSH1, AND>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
                if (MONAD_UNLIKELY(gas_remaining < 0)) {
                    MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
                }
    #endif
                auto &value = *stack_top;
                value[0] &= immediate;
                value[1] = 0;
                value[2] = 0;
                value[3] = 0;
                MONAD_VM_FUSED_NEXT(3, 0);
            }
            interpreter::push(stack_top, uint256_t{immediate});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == SIGNEXTEND) {
            // Extend the selected byte's sign within its 64-bit word, then
            // fill higher words with that sign. Lower words stay unchanged.
            // Keep a separate fast path for byte indices 0..7.
            uint8_t const immediate = *(instr_ptr + 1);
            if (MONAD_LIKELY(
                    stack_holds<1>(stack_top, stack_lower_bound) &&
                    immediate < 31)) {
                gas_remaining -= static_gas<traits, PUSH1, SIGNEXTEND>();
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
                if (MONAD_UNLIKELY(gas_remaining < 0)) {
                    MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
                }
    #endif
                auto &value = *stack_top;
                if (MONAD_LIKELY(immediate < 8)) {
                    unsigned const sign_shift = 56u - 8u * immediate;
                    int64_t const signed_word =
                        static_cast<int64_t>(value[0] << sign_shift) >>
                        sign_shift;
                    uint64_t const sign_fill =
                        static_cast<uint64_t>(signed_word >> 63);
                    value[0] = static_cast<uint64_t>(signed_word);
                    value[1] = sign_fill;
                    value[2] = sign_fill;
                    value[3] = sign_fill;
                }
                else {
                    unsigned const word_index = immediate >> 3;
                    unsigned const sign_shift = 56u - 8u * (immediate & 7u);
                    int64_t const signed_word =
                        static_cast<int64_t>(value[word_index] << sign_shift) >>
                        sign_shift;
                    uint64_t const sign_fill =
                        static_cast<uint64_t>(signed_word >> 63);
                    value[word_index] = static_cast<uint64_t>(signed_word);
                    if (word_index == 1) {
                        value[2] = sign_fill;
                        value[3] = sign_fill;
                    }
                    else if (word_index == 2) {
                        value[3] = sign_fill;
                    }
                }
                MONAD_VM_FUSED_NEXT(3, 0);
            }
            interpreter::push(stack_top, uint256_t{immediate});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            // Slots provide a known handler, avoiding a table lookup here.
            if constexpr (fallback_handler != nullptr) {
                MONAD_VM_MUST_TAIL return fallback_handler(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top + 1,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
            else {
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top + 1,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
        else {
            static_assert(OP == ADD || OP == SHL || OP == SHR || OP == SAR);
            // The pair replaces the top. Slot dispatch already checked
            // room for the temporary PUSH1 value.
            static constexpr auto pair_requirements = [] {
                auto requirements = fused_requirements<
                    traits,
                    PUSH1,
                    static_cast<compiler::EvmOpCode>(OP)>();
                if (has_slots<traits>) {
                    requirements.max_growth = 0;
                }
                return requirements;
            }();
            if (MONAD_UNLIKELY(
                    !MONAD_VM_FUSED_CHARGE_PURE(pair_requirements))) {
                gas_remaining += pair_requirements.gas;
                MONAD_VM_CHECK(PUSH1);
                MONAD_VM_CHECK_AT(OP, 1);
            }
            uint256_t const immediate{*(instr_ptr + 1)};
            if constexpr (OP == ADD) {
                *stack_top = immediate + *stack_top;
            }
            else if constexpr (OP == SHL) {
                *stack_top <<= immediate;
            }
            else if constexpr (OP == SHR) {
                // Dispatch each wide shift here so its stores stay on this
                // path.
                uint64_t const total_shift = immediate[0];
                unsigned const intra_word_shift =
                    static_cast<unsigned>(total_shift & 63);
                auto &value = *stack_top;
                if (total_shift >= 192) {
                    value[0] = value[3] >> intra_word_shift;
                    value[1] = 0;
                    value[2] = 0;
                    value[3] = 0;
                    MONAD_VM_FUSED_NEXT(3, 0);
                }
                if (total_shift >= 128) {
                    uint64_t const high_word = value[3];
                    // Splitting the left shift gives zero carry at exactly 128
                    // without shifting a 64-bit word by 64.
                    value[0] = (value[2] >> intra_word_shift) |
                               ((high_word << 1) << (63 - intra_word_shift));
                    value[1] = high_word >> intra_word_shift;
                    value[2] = 0;
                    value[3] = 0;
                    MONAD_VM_FUSED_NEXT(3, 0);
                }
                *stack_top >>= immediate;
            }
            else {
                *stack_top = sar(immediate, *stack_top);
            }
            MONAD_VM_FUSED_NEXT(3, 0);
        }
    }

    // Recognize this Solidity loop over [..., len, dst, src, i]:
    //   h: JUMPDEST DUP4 DUP2 LT ISZERO PUSH2 <end> JUMPI
    //      DUP2 DUP2 ADD MLOAD DUP4 DUP3 ADD MSTORE PUSH1 0x20 ADD
    //      PUSH2 <h> JUMP
    // Each turn copies 32 bytes from src+i to dst+i, then adds 32 to i.
    // Enter after a fall-through JUMPDEST, with instr_ptr on DUP4. Validate
    // the full pattern and bounds before batching copies and gas charges.
    // Unsupported cases resume ordinary dispatch without changing the frame.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void copy_loop(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        alignas(8) static constexpr uint8_t condition_pattern[8] = {
            static_cast<uint8_t>(LT),
            static_cast<uint8_t>(ISZERO),
            static_cast<uint8_t>(PUSH2)};
        alignas(8) static constexpr uint8_t copy_pattern[16] = {
            static_cast<uint8_t>(JUMPI),
            static_cast<uint8_t>(DUP2),
            static_cast<uint8_t>(DUP2),
            static_cast<uint8_t>(ADD),
            static_cast<uint8_t>(MLOAD),
            static_cast<uint8_t>(DUP4),
            static_cast<uint8_t>(DUP3),
            static_cast<uint8_t>(ADD),
            static_cast<uint8_t>(MSTORE),
            static_cast<uint8_t>(PUSH1),
            32,
            static_cast<uint8_t>(ADD),
            static_cast<uint8_t>(PUSH2)};
        auto const *const loop_instructions = instr_ptr;
        auto const fits_memory_offset = [](uint256_t const &x) {
            return (x[1] | x[2] | x[3]) == 0 && x[0] < (uint64_t{1} << 28);
        };
        // PUSH2 immediates at loop_instructions + 5 and loop_instructions + 20
        // encode the exit and loop PCs.
        size_t const exit_pc = detail::load_be_k<2>(loop_instructions + 5);
        size_t const loop_pc = detail::load_be_k<2>(loop_instructions + 20);
        // Check all four operands before forming references into the stack.
        if (!stack_holds<4>(stack_top, stack_lower_bound) ||
            stack_top.next_slot() > MONAD_VM_STACK_LIMIT - 3) {
            MONAD_VM_DISPATCH(0, 0, *instr_ptr);
        }
        uint256_t const &loop_index = stack_top[0];
        uint256_t const &source_offset = stack_top[-1];
        uint256_t const &destination_offset = stack_top[-2];
        uint256_t const &loop_end_index = stack_top[-3];
        // Entry through JUMPDEST guarantees the preceding opcode is JUMPDEST.
        // Compare fixed spans around the two variable jump destinations.
        // The copy span includes PUSH1 0x20; ADD (advance by 32 bytes).
        if (!(code_matches<3>(loop_instructions + 2, condition_pattern) &&
              code_matches<13>(loop_instructions + 7, copy_pattern) &&
              opcode_at_is(loop_instructions, 22, JUMP) &&
              // The back jump must target the JUMPDEST at the loop's start.
              loop_pc ==
                  static_cast<size_t>(
                      loop_instructions - 1 - MONAD_VM_CODE_VIEW.code()) &&
              fits_memory_offset(loop_end_index) &&
              fits_memory_offset(loop_index) &&
              fits_memory_offset(source_offset) &&
              fits_memory_offset(destination_offset) &&
              loop_index[0] < loop_end_index[0])) {
            MONAD_VM_DISPATCH(0, 0, *instr_ptr);
        }

        uint64_t const initial_index = loop_index[0];
        uint64_t const source_offset_u64 = source_offset[0];
        uint64_t const destination_offset_u64 = destination_offset[0];
        uint64_t const iteration_count =
            (loop_end_index[0] - initial_index + 31) >> 5;
        uint64_t const last_iteration_index =
            initial_index + 32 * (iteration_count - 1);
        // The furthest words' offsets are MLOAD's and MSTORE's: under 2^28.
        if (source_offset_u64 + last_iteration_index >= (uint64_t{1} << 28) ||
            destination_offset_u64 + last_iteration_index >=
                (uint64_t{1} << 28)) {
            MONAD_VM_DISPATCH(0, 0, *instr_ptr);
        }
        uint64_t const required_memory_size =
            std::max(source_offset_u64, destination_offset_u64) +
            last_iteration_index + 32;
        int64_t memory_expansion_gas = 0;
        auto new_memory_size = ctx.memory.size;
        auto new_memory_cost = ctx.memory.cost;
        if (required_memory_size > ctx.memory.size) {
            auto const required_word_count =
                runtime::Context::memory_size_to_word_count(
                    runtime::Bin<29>::unsafe_from(required_memory_size));
            auto const rounded_memory_size =
                runtime::Context::word_count_to_memory_size(
                    required_word_count);
            if (MONAD_UNLIKELY(
                    ctx.memory.capacity < *rounded_memory_size ||
                    !ctx.is_memory_size_in_bound<traits>(
                        rounded_memory_size))) {
                MONAD_VM_DISPATCH(0, 0, *instr_ptr);
            }
            auto const expanded_memory_cost =
                runtime::Context::memory_cost_from_word_count<traits>(
                    required_word_count);
            memory_expansion_gas = expanded_memory_cost - ctx.memory.cost;
            new_memory_size = *rounded_memory_size;
            new_memory_cost = expanded_memory_cost;
        }
        // A turn from the head's DUP4 to the next head, and the exit.
        static constexpr int64_t iteration_gas = static_gas<
            traits,
            DUP4,
            DUP2,
            LT,
            ISZERO,
            PUSH2,
            JUMPI,
            DUP2,
            DUP2,
            ADD,
            MLOAD,
            DUP4,
            DUP3,
            ADD,
            MSTORE,
            PUSH1,
            ADD,
            PUSH2,
            JUMP,
            JUMPDEST>();
        static constexpr int64_t exit_gas = static_gas<
            traits,
            DUP4,
            DUP2,
            LT,
            ISZERO,
            PUSH2,
            JUMPI,
            JUMPDEST>();
        gas_remaining -= iteration_gas * static_cast<int64_t>(iteration_count) +
                         exit_gas + memory_expansion_gas;
        if (MONAD_UNLIKELY(!MONAD_VM_CODE_VIEW.is_jumpdest16(exit_pc))) {
            MONAD_VM_MUST_TAIL return ctx.exit(Error);
        }
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        ctx.memory.size = new_memory_size;
        ctx.memory.cost = new_memory_cost;
        uint8_t *const memory_data = ctx.memory.data;
        uint64_t const copy_byte_count = 32 * iteration_count;
        // The turns read no word an earlier one wrote when the ranges are
        // apart: one copy. Otherwise word by word, in their order.
        if (destination_offset_u64 + copy_byte_count <= source_offset_u64 ||
            source_offset_u64 + copy_byte_count <= destination_offset_u64) {
            std::memcpy(
                memory_data + destination_offset_u64 + initial_index,
                memory_data + source_offset_u64 + initial_index,
                copy_byte_count);
        }
        else {
            for (uint64_t k = initial_index; k <= last_iteration_index;
                 k += 32) {
                uint64_t copied_word[4];
                std::memcpy(
                    copied_word, memory_data + source_offset_u64 + k, 32);
                std::memcpy(
                    memory_data + destination_offset_u64 + k, copied_word, 32);
            }
        }
        // Leave the index at or beyond the loop bound, as ordinary execution
        // does.
        stack_top[0] = uint256_t{last_iteration_index + 32};
        instr_ptr = MONAD_VM_CODE_VIEW.code() + exit_pc + 1;
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // The end of Solidity's finalize_allocation,
    //
    //     PUSH8 0xffffffffffffffff DUP3 GT OR PUSH2 <panic> JUMPI
    //     PUSH1 0x40 MSTORE JUMP
    //
    // Stack: [..., return address, new free memory pointer, overflow flag].
    // Fuse only the successful path with memory already covering [0x40, 0x60).
    // Other cases execute PUSH8 here, then resume ordinary dispatch.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push8_alloc(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        alignas(8) static constexpr uint8_t limit_pattern[16] = {
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            static_cast<uint8_t>(DUP3),
            static_cast<uint8_t>(GT),
            static_cast<uint8_t>(OR),
            static_cast<uint8_t>(PUSH2)};
        alignas(8) static constexpr uint8_t store_pattern[8] = {
            static_cast<uint8_t>(JUMPI),
            static_cast<uint8_t>(PUSH1),
            64,
            static_cast<uint8_t>(MSTORE),
            static_cast<uint8_t>(JUMP)};
        auto const *const instructions = instr_ptr;
        // Validate the three operands and two temporary slots before reading.
        if (!stack_holds<3>(stack_top, stack_lower_bound) ||
            stack_top.next_slot() > MONAD_VM_STACK_LIMIT - 2) {
            MONAD_VM_CHECK(PUSH8);
            push_impl<8, traits>::push(stack_top, instr_ptr);
            MONAD_VM_NEXT_PUSH(PUSH8);
        }
        uint256_t const &pointer_wrapped = stack_top[0];
        uint256_t const &free_memory_pointer = stack_top[-1];
        uint256_t const &return_address = stack_top[-2];
        auto const return_pc = static_cast<size_t>(return_address[0]);
        // Skip the variable panic destination between the fixed spans.
        if (!(code_matches<12>(instructions + 1, limit_pattern) &&
              code_matches<5>(instructions + 15, store_pattern) &&
              (pointer_wrapped[0] | pointer_wrapped[1] | pointer_wrapped[2] |
               pointer_wrapped[3]) == 0 &&
              (free_memory_pointer[1] | free_memory_pointer[2] |
               free_memory_pointer[3]) == 0 &&
              ctx.memory.size >= 0x60 &&
              (return_address[1] | return_address[2] | return_address[3]) ==
                  0 &&
              MONAD_VM_CODE_VIEW.is_jumpdest(return_pc))) {
            // Execute PUSH8 directly to avoid re-entering this helper.
            MONAD_VM_CHECK(PUSH8);
            push_impl<8, traits>::push(stack_top, instr_ptr);
            MONAD_VM_NEXT_PUSH(PUSH8);
        }
        static constexpr int64_t sequence_gas = static_gas<
            traits,
            PUSH8,
            DUP3,
            GT,
            OR,
            PUSH2,
            JUMPI,
            PUSH1,
            MSTORE,
            JUMP,
            JUMPDEST>();
        gas_remaining -= sequence_gas;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        runtime::mstore_at<traits>(
            &ctx,
            runtime::Memory::Offset::unsafe_from(0x40),
            &free_memory_pointer);
        instr_ptr = MONAD_VM_CODE_VIEW.code() + return_pc + 1;
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top - 3,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // Fuse PUSH4/PUSH20 <mask> AND: replace the top value with value & mask.
    // Keep this helper separate to limit register pressure in ordinary PUSHs.
    template <size_t N, Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push_and(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        static constexpr auto requirements = fused_requirements<
            traits,
            static_cast<compiler::EvmOpCode>(PUSH0 + N),
            AND>();
        if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
            gas_remaining += requirements.gas;
            MONAD_VM_CHECK(PUSH0 + N);
            MONAD_VM_CHECK_AT(AND, 1);
        }
        auto &value = *stack_top;
        if constexpr (N == 4) {
            value[0] &= detail::load_be_k<4>(instr_ptr + 1);
            value[1] = 0;
            value[2] = 0;
            value[3] = 0;
        }
        else {
            static_assert(N == 20);
            // PUSH20 stores the mask big-endian, most significant bytes first:
            // offset: 0       1..4       5..12      13..20     21
            //         PUSH20  [word 2]   [word 1]   [word 0]   AND
            value[0] &= detail::read_unaligned(instr_ptr + 13);
            value[1] &= detail::read_unaligned(instr_ptr + 5);
            value[2] &= detail::load_be_k<4>(instr_ptr + 1);
            value[3] = 0;
        }
        MONAD_VM_FUSED_NEXT(N + 2, 0);
    }

#endif

    template <size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Code padding makes lookahead safe. Reuse the follower opcode
        // for fusion checks, prefix dispatch and ordinary dispatch.
        [[maybe_unused]] uint8_t next_opcode = 0;
        if constexpr (N == 1 || N == 2 || N == 4 || N == 8 || N == 20) {
            next_opcode = *(instr_ptr + N + 1);
        }
        if constexpr (N == 1 && has_slots<traits>) {
            // Enter the follower's prefix: it executes PUSH1 then falls
            // through, or jumps to a fused pair. Check stack space first.
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
            // The prefix charges 3 gas; eager mode must reject before writing.
            if (MONAD_UNLIKELY(gas_remaining < 3)) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
    #endif
            if (MONAD_UNLIKELY(stack_top.next_slot() >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            MONAD_VM_PUSH1_PREFIX_DISPATCH(
                next_opcode, stack_top, gas_remaining, instr_ptr);
        }
        else if constexpr (N == 1) {
            // A bitmap keeps the check cheap on every PUSH1; testing four
            // opcodes separately regressed performance.
            constexpr std::uint64_t monad_vm_fuse_mask =
                (1ull << static_cast<unsigned>(ADD)) |
                (1ull << static_cast<unsigned>(SHL)) |
                (1ull << static_cast<unsigned>(SHR)) |
                (1ull << static_cast<unsigned>(SAR));
            // PUSH1 (handled below) and DUP2 exceed this mask's range.
            // Filtering for these four opcodes first improves performance.
            if (next_opcode < 64 && ((monad_vm_fuse_mask >> next_opcode) & 1)) {
                // These four followers share gas and stack requirements.
                // Verify that ADD's checks cover all four.
                static constexpr auto requirements =
                    fused_requirements<traits, PUSH1, ADD>();
                static_assert(
                    requirements == fused_requirements<traits, PUSH1, SHL>() &&
                        requirements ==
                            fused_requirements<traits, PUSH1, SHR>() &&
                        requirements ==
                            fused_requirements<traits, PUSH1, SAR>(),
                    "PUSH1 fusion mask holds followers with unequal "
                    "requirements; aggregate them per follower");
                if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
                    gas_remaining += requirements.gas;
                    MONAD_VM_CHECK(PUSH1);
                    MONAD_VM_CHECK_AT(ADD, 1);
                }
                uint256_t const immediate{*(instr_ptr + 1)};
                if (next_opcode == static_cast<std::uint8_t>(ADD)) {
                    *stack_top = immediate + *stack_top;
                }
                else if (next_opcode == static_cast<std::uint8_t>(SHL)) {
                    *stack_top <<= immediate;
                }
                else if (next_opcode == static_cast<std::uint8_t>(SHR)) {
                    MONAD_VM_MUST_TAIL return push1_shr<traits>(
                        ctx,
                        MONAD_VM_DISPATCH_STATE_ARG,
                        stack_lower_bound,
                        stack_top,
                        gas_remaining,
                        instr_ptr MONAD_VM_TBL_ARG);
                }
                else {
                    MONAD_VM_MUST_TAIL return push1_sar<traits>(
                        ctx,
                        MONAD_VM_DISPATCH_STATE_ARG,
                        stack_lower_bound,
                        stack_top,
                        gas_remaining,
                        instr_ptr MONAD_VM_TBL_ARG);
                }
                // Advance instr_ptr by 3 bytes, keep the stack size unchanged,
                // and call the next opcode handler.
                // Returns from the current handler.
                MONAD_VM_FUSED_NEXT(3, 0);
            }
            // PUSH1 <a> PUSH1 <b>, tested outside of the previous mask
            // because PUSH1 is #96 > 64.
            if (next_opcode == static_cast<std::uint8_t>(PUSH1)) {
                MONAD_VM_MUST_TAIL return push1_then<PUSH1, traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
        // Use PUSH2's immediate directly as the jump destination.
        if constexpr (N == 2) {
            // Match JUMP and JUMPI with one range check: they are consecutive.
            // size_t and not unsigned for the difference: a 32-bit subtract
            // puts this on ZisK's generic binary machine on every PUSH2.
            auto const monad_vm_jump =
                static_cast<size_t>(next_opcode) - static_cast<size_t>(JUMP);
            if (monad_vm_jump <= 1u) {
                if (monad_vm_jump == 0) {
                    {
                        // Decode PUSH2's destination with the shared big-endian
                        // reader to favor the cheaper packh sequence on ZisK.
                        auto const destination = static_cast<size_t>(
                            detail::load_be_k<2>(instr_ptr + 1));
                        // Include the destination JUMPDEST in the upfront gas
                        // charge.
                        static constexpr auto requirements =
                            fused_requirements<traits, PUSH2, JUMP, JUMPDEST>();
                        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(requirements))) {
                            if (MONAD_UNLIKELY(
                                    !MONAD_VM_CODE_VIEW.is_jumpdest16(
                                        destination))) {
                                ctx.exit(Error);
                            }
                            instr_ptr =
                                MONAD_VM_CODE_VIEW.code() + destination + 1;
                            // Discourage GCC from copying the destination
                            // before the add.
                            MONAD_VM_LAUNDER(instr_ptr);
                        }
                        else {
                            gas_remaining += requirements.gas;
                            MONAD_VM_CHECK(PUSH2);
                            // PUSH2 supplies the operand required by JUMP.
                            MONAD_DEBUG_ASSERT(
                                stack_top.next_slot() >=
                                stack_lower_bound -
                                    MONAD_VM_STACK_LOWER_BOUND_BIAS);
                            MONAD_VM_CHARGE(JUMP);
                            if (MONAD_UNLIKELY(
                                    !MONAD_VM_CODE_VIEW.is_jumpdest16(
                                        destination))) {
                                ctx.exit(Error);
                            }
                            instr_ptr = swallow_jumpdest(
                                ctx,
                                MONAD_VM_CODE_VIEW.code() + destination,
                                gas_remaining);
                        }
                        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF
                            [*instr_ptr](
                                ctx,
                                MONAD_VM_DISPATCH_STATE_ARG,
                                stack_lower_bound,
                                stack_top,
                                gas_remaining,
                                instr_ptr MONAD_VM_TBL_ARG);
                    }
                }
                {
                    static constexpr auto jump_requirements =
                        fused_requirements<traits, PUSH2, JUMPI>();
                    if (MONAD_UNLIKELY(
                            !MONAD_VM_FUSED_CHARGE_PURE(jump_requirements))) {
                        gas_remaining += jump_requirements.gas;
                        MONAD_VM_CHECK(PUSH2);
                        MONAD_VM_CHECK_AT(JUMPI, 1);
                    }
                    // Keep the sequence's gas deduction before the branch to
                    // avoid extra register moves when dispatching either
                    // outcome.
                    MONAD_VM_LAUNDER(gas_remaining);
                    // The condition is the original top, below PUSH2's
                    // destination.
                    if (*stack_top) {
                        // An untaken jump does not need its destination
                        // decoded.
                        auto const destination = static_cast<size_t>(
                            detail::load_be_k<2>(instr_ptr + 1));
                        if (MONAD_UNLIKELY(!MONAD_VM_CODE_VIEW.is_jumpdest16(
                                destination))) {
                            ctx.exit(Error);
                        }
                        auto const *next_instruction =
                            MONAD_VM_CODE_VIEW.code() + destination;
                        next_instruction = swallow_jumpdest(
                            ctx, next_instruction, gas_remaining);
                        instr_ptr = next_instruction;
                        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF
                            [*instr_ptr](
                                ctx,
                                MONAD_VM_DISPATCH_STATE_ARG,
                                stack_lower_bound,
                                stack_top - 1, // Consume JUMPI's condition.
                                gas_remaining,
                                instr_ptr MONAD_VM_TBL_ARG);
                    }
                    // Skip the pair and consume the condition when the jump is
                    // not taken.
                    MONAD_VM_FUSED_NEXT(4, -1);
                }
            }
        }
        // Check the full allocation suffix in a separate helper.
    #if !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        if constexpr (N == 8) {
            if (next_opcode == static_cast<std::uint8_t>(DUP3)) {
                MONAD_VM_MUST_TAIL return push8_alloc<traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
    #endif
        // PUSH4 <mask> AND and PUSH20 <mask> AND in their twin.
        if constexpr (N == 4 || N == 20) {
            if (next_opcode == static_cast<std::uint8_t>(AND)) {
                MONAD_VM_MUST_TAIL return push_and<N, traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
#endif
        MONAD_VM_CHECK(PUSH0 + N);
        push_impl<N, traits>::push(stack_top, instr_ptr);

#if defined(MONAD_ZKVM_ZISK)
        if constexpr (N == 1 || N == 2 || N == 4 || N == 8 || N == 20) {
            MONAD_VM_NEXT_PUSH_OP(PUSH0 + N, next_opcode);
        }
#endif
        MONAD_VM_NEXT_PUSH(PUSH0 + N);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(POP);
        MONAD_VM_NEXT(POP);
    }

    template <std::ptrdiff_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse DUP1 PUSH4 <selector> EQ PUSH2 <dst> JUMPI without temporary
        // stack writes. Fusing only DUP1/PUSH4/EQ would prevent the existing
        // EQ/PUSH2/JUMPI fusion.
        // Keep the next opcode for the unfused path to avoid reloading it.
        [[maybe_unused]] uint8_t next_opcode = 0;
        if constexpr (N == 1) {
            next_opcode = *(instr_ptr + 1);
            // Check PUSH4 first; Intercode's tail padding makes lookahead
            // through instr_ptr[10] safe.
            if (next_opcode == static_cast<std::uint8_t>(PUSH4) &&
                *(instr_ptr + 6) == static_cast<std::uint8_t>(EQ) &&
                *(instr_ptr + 7) == static_cast<std::uint8_t>(PUSH2) &&
                *(instr_ptr + 10) == static_cast<std::uint8_t>(JUMPI)) {
                static constexpr auto requirements =
                    fused_requirements<traits, DUP1, PUSH4, EQ, PUSH2, JUMPI>();
                if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
                    gas_remaining += requirements.gas;
                    MONAD_VM_CHECK(DUP1);
                    MONAD_VM_CHECK_AT(PUSH4, 1);
                    MONAD_VM_CHECK_AT(EQ, 2);
                    MONAD_VM_CHECK_AT(PUSH2, 1);
                    MONAD_VM_CHECK_AT(JUMPI, 2);
                }
                // Keep the gas deduction before the branch, as in push2_jumpi.
                MONAD_VM_LAUNDER(gas_remaining);
                // Byte offsets within each 11-byte selector test:
                //   0     1      2..5       6   7      8..9         10
                //   DUP1  PUSH4  [selector] EQ  PUSH2  [destination] JUMPI
                // Compare the selector at +2 with the value on the stack.
                // A failed test preserves that value for the next test.
                while (uint256_t{detail::load_be_k<4>(instr_ptr + 2)} !=
                       *stack_top) {
                    instr_ptr += 11; // Skip the entire failed test.
                    // Continue the loop only if the next bytes form another
                    // selector test; otherwise leave via normal dispatch.
                    // Tail padding makes these lookahead reads safe.
                    if (*instr_ptr != static_cast<std::uint8_t>(DUP1) ||
                        *(instr_ptr + 1) != static_cast<std::uint8_t>(PUSH4) ||
                        *(instr_ptr + 6) != static_cast<std::uint8_t>(EQ) ||
                        *(instr_ptr + 7) != static_cast<std::uint8_t>(PUSH2) ||
                        *(instr_ptr + 10) != static_cast<std::uint8_t>(JUMPI)) {
                        MONAD_VM_DISPATCH(0, 0, *instr_ptr);
                    }
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
                    // The first test validated the unchanged stack.
                    MONAD_VM_CHARGE(DUP1);
                    MONAD_VM_CHARGE(PUSH4);
                    MONAD_VM_CHARGE(EQ);
                    MONAD_VM_CHARGE(PUSH2);
                    MONAD_VM_CHARGE(JUMPI);
    #else
                    gas_remaining -= requirements.gas;
    #endif
                }
                // A selector matched: take its jump. fused_branch expects
                // the EQ at +6, followed by PUSH2 <dst> JUMPI.
                instr_ptr =
                    fused_branch(ctx, instr_ptr + 6, true, gas_remaining);
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
            // Split the selector search around a pivot:
            //   0     1      2..5    6   7      8..9         10
            //   DUP1  PUSH4  [pivot] GT  PUSH2  [destination] JUMPI
            // GT compares the top (pivot) with the value below (selector),
            // so the jump is taken when selector < pivot.
            if (next_opcode == static_cast<std::uint8_t>(PUSH4) &&
                *(instr_ptr + 6) == static_cast<std::uint8_t>(GT) &&
                *(instr_ptr + 7) == static_cast<std::uint8_t>(PUSH2) &&
                *(instr_ptr + 10) == static_cast<std::uint8_t>(JUMPI)) {
                static constexpr auto requirements =
                    fused_requirements<traits, DUP1, PUSH4, GT, PUSH2, JUMPI>();
                if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(requirements))) {
                    gas_remaining += requirements.gas;
                    MONAD_VM_CHECK(DUP1);
                    MONAD_VM_CHECK_AT(PUSH4, 1);
                    MONAD_VM_CHECK_AT(GT, 2);
                    MONAD_VM_CHECK_AT(PUSH2, 1);
                    MONAD_VM_CHECK_AT(JUMPI, 2);
                }
                MONAD_VM_LAUNDER(gas_remaining);
                bool const take_jump =
                    (uint256_t{detail::load_be_k<4>(instr_ptr + 2)} >
                     *stack_top);
                instr_ptr =
                    fused_branch(ctx, instr_ptr + 6, take_jump, gas_remaining);
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
#endif
#if defined(MONAD_ZKVM_ZISK)
        if constexpr (N == 1) {
            MONAD_VM_CHECK(DUP1);

            push(stack_top, *stack_top);

            MONAD_VM_NEXT_OP(DUP1, next_opcode);
        }
        else {
            MONAD_VM_CHECK_OWN_OVERFLOW(DUP1 + (N - 1));

            push(stack_top, stack_top[-(N - 1)]);

            MONAD_VM_NEXT(DUP1 + (N - 1));
        }
#else
        MONAD_VM_CHECK(DUP1 + (N - 1));

        push(stack_top, stack_top[-(N - 1)]);

        MONAD_VM_NEXT(DUP1 + (N - 1));
#endif
    }

    [[gnu::always_inline]] inline void
    swap_slots(uint256_t &a, uint256_t &b) noexcept
    {
#ifdef __AVX2__
        auto const t = a.to_avx();
        a = b;
        b = uint256_t{t};
#else
        std::swap(a, b);
#endif
    }

    template <std::ptrdiff_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SWAP1 + (N - 1));

#if defined(MONAD_ZKVM_ZISK)
        // Reuse Context's scratch slot to avoid a local 32-byte stack frame.
        {
            uint256_t *const monad_t = &ctx.swap_scratch;
            *monad_t = *stack_top;
            *stack_top = stack_top[-static_cast<std::ptrdiff_t>(N)];
            stack_top[-static_cast<std::ptrdiff_t>(N)] = *monad_t;
        }
#else
        // Keep the temporary as uint256_t to avoid an AVX round trip.
        uint256_t const top = *stack_top;
        *stack_top = stack_top[-static_cast<std::ptrdiff_t>(N)];
        stack_top[-static_cast<std::ptrdiff_t>(N)] = top;
#endif

        MONAD_VM_NEXT(SWAP1 + (N - 1));
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void dupn(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const ops = check_requirements_eip8024<DUPN, traits>(
            ctx, stack_lower_bound, stack_top, gas_remaining, instr_ptr[1]);

        push(stack_top, stack_top[-(ops.n - 1)]);

        MONAD_VM_NEXT_IMM(DUPN);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swapn(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const ops = check_requirements_eip8024<SWAPN, traits>(
            ctx, stack_lower_bound, stack_top, gas_remaining, instr_ptr[1]);

        swap_slots(*stack_top, stack_top[-ops.n]);

        MONAD_VM_NEXT_IMM(SWAPN);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void exchange(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const ops = check_requirements_eip8024<EXCHANGE, traits>(
            ctx, stack_lower_bound, stack_top, gas_remaining, instr_ptr[1]);

        swap_slots(stack_top[-ops.n], stack_top[-ops.m]);

        MONAD_VM_NEXT_IMM(EXCHANGE);
    }

    // Control Flow
    namespace
    {
        template <typename Analysis>
        inline uint8_t const *jump_impl(
            runtime::Context &ctx, Analysis const &analysis,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Include the destination JUMPDEST in the upfront gas charge.
        static constexpr auto requirements =
            fused_requirements<traits, JUMP, JUMPDEST>();
        uint8_t const *new_ip;
        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(requirements))) {
            auto const &target = pop(stack_top);
            new_ip = jump_impl(ctx, MONAD_VM_CODE_VIEW, target) + 1;
        }
        else {
            gas_remaining += requirements.gas;
            MONAD_VM_CHECK(JUMP);
            auto const &target = pop(stack_top);
            new_ip = swallow_jumpdest(
                ctx, jump_impl(ctx, MONAD_VM_CODE_VIEW, target), gas_remaining);
        }
#else
        MONAD_VM_CHECK(JUMP);
        auto const &target = pop(stack_top);
        auto const *new_ip = jump_impl(ctx, MONAD_VM_CODE_VIEW, target);
#endif

        if constexpr (debug_enabled) {
            trace(MONAD_VM_CODE_VIEW, gas_remaining, new_ip);
        }
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            new_ip MONAD_VM_TBL_ARG);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(JUMPI);
        auto const &target = pop(stack_top);
        auto const &cond = pop(stack_top);

        if (cond) {
            auto const *new_ip = jump_impl(ctx, MONAD_VM_CODE_VIEW, target);
#if defined(MONAD_ZKVM_ZISK)
            new_ip = swallow_jumpdest(ctx, new_ip, gas_remaining);
#endif
            if constexpr (debug_enabled) {
                trace(MONAD_VM_CODE_VIEW, gas_remaining, new_ip);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                new_ip MONAD_VM_TBL_ARG);
        }
        else {
            ++instr_ptr;
            if constexpr (debug_enabled) {
                trace(MONAD_VM_CODE_VIEW, gas_remaining, instr_ptr);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        fuzz_tstore_stack(
            ctx,
            stack_lower_bound,
            stack_top,
            static_cast<uint64_t>(instr_ptr - MONAD_VM_CODE_VIEW.code()));
        MONAD_VM_CHECK(JUMPDEST);

#if defined(MONAD_ZKVM_ZISK) && !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        // Falling through into DUP4 DUP2 may enter a memory copy loop, which
        // copy_loop runs whole: the dispatch's target, as push1_mask's.
        instr_ptr += 1;
        MONAD_VM_LAUNDER(instr_ptr);
        bool const monad_vm_loop =
            *instr_ptr == static_cast<std::uint8_t>(DUP4) &&
            *(instr_ptr + 1) == static_cast<std::uint8_t>(DUP2);
        auto const monad_vm_next =
            monad_vm_loop ? &copy_loop<traits> : MONAD_VM_TABLE_REF[*instr_ptr];
        MONAD_VM_MUST_TAIL return monad_vm_next(
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
#else
        MONAD_VM_NEXT(JUMPDEST);
#endif
    }

    // Logging
    template <size_t N, Traits traits>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void
    log(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CREATE, runtime::create<traits>);

        MONAD_VM_NEXT(CREATE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALL, runtime::call<traits>);

        MONAD_VM_NEXT(CALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALLCODE, runtime::callcode<traits>);

        MONAD_VM_NEXT(CALLCODE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            DELEGATECALL, runtime::delegatecall<traits>);

        MONAD_VM_NEXT(DELEGATECALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CREATE2, runtime::create2<traits>);

        MONAD_VM_NEXT(CREATE2);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(STATICCALL, runtime::staticcall<traits>);

        MONAD_VM_NEXT(STATICCALL);
    }

    // VM Control
    namespace
    {
        // On ZisK, STOP/RETURN/REVERT return through the tail-call chain
        // to the trampoline, avoiding longjmp's register reloads.
        // Exits from runtime calls still use ctx.exit to unwind.
        inline void
        handler_exit(runtime::Context &ctx, runtime::StatusCode const code)
        {
#if defined(MONAD_ZKVM_ZISK)
            ctx.result.status = code;
#else
            ctx.exit(code);
#endif
        }

        inline void return_impl(
            runtime::StatusCode const code, runtime::Context &ctx,
            StackTop stack_top, int64_t const gas_remaining)
        {
#if defined(MONAD_ZKVM_ZISK)
            // Reject deferred gas exhaustion before returning or reverting.
            if (MONAD_UNLIKELY(gas_remaining < 0)) {
                ctx.exit(OutOfGas);
            }
#endif
            for (auto *result_loc : {&ctx.result.offset, &ctx.result.size}) {
                std::copy_n(
                    as_bytes(*stack_top),
                    32,
                    reinterpret_cast<uint8_t *>(result_loc));

                --stack_top;
            }

            ctx.gas_remaining = gas_remaining;
            handler_exit(ctx, code);
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void return_(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(
            ctx, stack_lower_bound, stack_top, MONAD_VM_CODE_VIEW.size());
        MONAD_VM_CHECK(RETURN);
        return_impl(Success, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &ctx, [[maybe_unused]] MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        MONAD_VM_CHECK(REVERT);
        return_impl(Revert, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(
            ctx, stack_lower_bound, stack_top, MONAD_VM_CODE_VIEW.size());
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SELFDESTRUCT, runtime::selfdestruct<traits>);
    }

    MONAD_VM_INLINE_INSTRUCTION_CALL void stop(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *const stack_lower_bound, StackTop const stack_top,
        int64_t const gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(
            ctx, stack_lower_bound, stack_top, MONAD_VM_CODE_VIEW.size());
#if defined(MONAD_ZKVM_ZISK)
        // Reject deferred gas exhaustion before reporting success.
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }
#endif
        ctx.gas_remaining = gas_remaining;
        handler_exit(ctx, Success);
    }

    MONAD_VM_INLINE_INSTRUCTION_CALL void invalid(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_TYPE, uint256_t const *,
        StackTop, int64_t const gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
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
#undef MONAD_VM_NEXT_OP
#undef MONAD_VM_NEXT_PUSH
#undef MONAD_VM_NEXT_IMM
#undef MONAD_VM_NEXT_PUSH_OP
#undef MONAD_VM_CHECK
#undef MONAD_VM_CHECK_AT
#undef MONAD_VM_CHARGE
#undef MONAD_VM_FUSED_CHARGE
#undef MONAD_VM_FUSED_CHARGE_PURE
#undef MONAD_VM_CHECKED_RUNTIME_CALL

#if defined(MONAD_ZKVM_ZISK)
    #undef MONAD_VM_PUSH1_PREFIX_DISPATCH
#endif
