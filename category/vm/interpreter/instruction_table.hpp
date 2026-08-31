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

// Dispatch after a fused sequence: NBYTES of code consumed and DELTA of net stack
// movement, both counted over every opcode the handler just executed.
#define MONAD_VM_FUSED_NEXT(NBYTES, DELTA)                                     \
    do {                                                                       \
        instr_ptr += (NBYTES);                                                 \
        if constexpr (debug_enabled) {                                         \
            trace(analysis, gas_remaining, instr_ptr);                         \
        }                                                                      \
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](              \
            ctx,                                                               \
            analysis,                                                          \
            stack_bottom,                                                      \
            stack_top + (DELTA),                                               \
            gas_remaining,                                                     \
            instr_ptr MONAD_VM_TBL_ARG);                                       \
    }                                                                          \
    while (false)

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
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](              \
            ctx,                                                               \
            analysis,                                                          \
            stack_bottom,                                                      \
            stack_top + delta,                                                 \
            gas_remaining,                                                     \
            instr_ptr MONAD_VM_TBL_ARG);                                       \
    }                                                                          \
    while (false);

// The gas and stack checks, as a macro rather than a call.
//
// check_requirements() is [[gnu::always_inline]] and its ctx.exit() calls are
// noreturn — but a noreturn *call* is still a `jal`, which clobbers `ra`, and
// `ra` is live across the whole handler because the dispatch at the end is a
// tail jump that must return to *our* caller. So GCC saves and restores it:
// `addi sp,sp,-16 / sd ra,8(sp) ... ld ra,8(sp) / addi sp,sp,16`, four
// instructions of frame on every opcode, including ones like ADD that call
// nothing on the fast path.
//
// Tail-calling the exit removes the clobber and the frame with it. musttail
// has to be *lexically* in the handler to survive: marking it inside
// check_requirements compiles, but the inliner drops it and the frame comes
// back — measured, 27 instructions with the frame either way, against 23
// with the macro. That is the same reason MONAD_VM_NEXT is a macro.
//
// Behaviour is unchanged: same conditions, same StatusCode, same
// Context::exit. Only the call instruction differs (`j` for `jal`) and the
// frame is torn down first — which is safe because Context::exit longjmps,
// restoring sp from the jmp_buf rather than unwinding through our frame.
//
// Worth 4 instructions x 1,069,980 opcodes on block 25551991 = 4.3 M steps,
// 3.3 % of the current guest.
#define MONAD_VM_CHECK(OP) MONAD_VM_CHECK_AT(OP, 0)

// SHIFT is the stack movement of operands already executed in this handler: a fused
// follower must be checked against the stack its predecessor leaves, not the one the
// handler was entered with. SHIFT 0 is the ordinary single-opcode case.
#define MONAD_VM_CHECK_AT(OP, SHIFT)                                           \
    do {                                                                       \
        static constexpr auto monad_vm_ci = compiler::opcode_table<traits>[(OP)]; \
                                                                               \
        if constexpr (monad_vm_ci.min_gas > 0) {                               \
            gas_remaining -= monad_vm_ci.min_gas;                              \
            if (MONAD_UNLIKELY(gas_remaining < 0)) {                           \
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);                  \
            }                                                                  \
        }                                                                      \
                                                                               \
        if constexpr (!(monad_vm_ci.min_stack == 0 &&                          \
                        monad_vm_ci.stack_increase == 0)) {                    \
            /* The height is only ever compared against compile-time bounds,   \
             * so compare the POINTER against `stack_bottom + bound` instead   \
             * of differencing first. Same comparisons, same branches, same    \
             * instruction count -- but the difference is a `sub`, which ZisK  \
             * prices through the generic binary machine at BINARY_COST = 60,  \
             * where an add has its own path at BINARY_ADD_COST = 25 and       \
             * measures 15.4 on average. 1,224,298 of these a block on         \
             * 25815091, 0.981 per dispatch. */                                \
            uint256_t const *const monad_vm_top = (stack_top) + (SHIFT);       \
            MONAD_DEBUG_ASSERT(monad_vm_top - stack_bottom <= 1024);           \
                                                                               \
            if constexpr (monad_vm_ci.min_stack > 0) {                         \
                if (MONAD_UNLIKELY(                                            \
                        monad_vm_top < stack_bottom + monad_vm_ci.min_stack)) {\
                    MONAD_VM_MUST_TAIL return ctx.exit(Error);                 \
                }                                                              \
            }                                                                  \
                                                                               \
            if constexpr (monad_vm_ci.stack_increase > 0) {                    \
                static constexpr auto monad_vm_delta =                         \
                    monad_vm_ci.stack_increase - monad_vm_ci.min_stack;        \
                /* `top > bottom + (1024 - d)` and `top >= bottom + (1025 -    \
                 * d)` are the same predicate, and the second is one           \
                 * instruction cheaper at the delta that matters. Every        \
                 * opcode in category/vm/evm/opcodes.hpp with a positive       \
                 * delta has it EXACTLY 1 -- 65 of them, none larger -- so     \
                 * the constant is 1024 slots = 32768 bytes at every emitted   \
                 * site, and 32768 is `lui rd,0x8` on its own. The 1023 form   \
                 * needs `lui` + `addi -32`. evmone's bound is already in      \
                 * this form, which is why its check is three instructions     \
                 * and ours was four.                                          \
                 *                                                             \
                 * `stack_bottom + 1024` is `&stack_ptr[1023]`, the last slot  \
                 * of the 1024-element buffer, so no out-of-bounds pointer is  \
                 * formed. Nothing is elided: the same comparison decides. */  \
                static constexpr auto monad_vm_limit =                         \
                    1025 - monad_vm_delta;                                     \
                if constexpr (monad_vm_limit <= 1024) {                        \
                    if (MONAD_UNLIKELY(                                        \
                            monad_vm_top >= stack_bottom + monad_vm_limit)) {  \
                        MONAD_VM_MUST_TAIL return ctx.exit(Error);             \
                    }                                                          \
                }                                                              \
            }                                                                  \
        }                                                                      \
    }                                                                          \
    while (false)

// Charge an opcode's gas and skip its stack check.
//
// Legal ONLY where the stack condition `MONAD_VM_CHECK_AT` would test cannot
// hold, and the caller must state the proof. This does not fail closed: getting
// it wrong deletes a bounds check and the interpreter runs off the stack, so a
// site that is merely believed safe belongs in MONAD_VM_CHECK_AT instead. Each
// use below carries a MONAD_DEBUG_ASSERT of the invariant it leans on, which is
// what a debug build has instead of the check.
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

// The fused fast path: test the whole sequence's requirements without mutating
// anything, and only then charge the aggregate gas. Testing before mutating is
// what lets the else-branch run the per-opcode checks against the state they
// expect, so the fallback reports the same error, at the same opcode, with the
// same gas remaining as it does today.
//
// The comparisons are the pointer form for the reason given on
// MONAD_VM_CHECK_AT, and the two bounds are elided when the sequence cannot
// underflow or cannot grow -- which for EQ PUSH2 JUMPI removes the overflow test
// altogether, EQ having popped two before the PUSH2 pushes one.
#define MONAD_VM_FUSED_OK(REQ)                                                 \
    ((gas_remaining >= (REQ).gas) &&                                           \
     ((REQ).min_required == 0 ||                                               \
      (stack_top) >= (stack_bottom) + (REQ).min_required) &&                   \
     ((REQ).max_growth == 0 ||                                                 \
      (stack_top) < (stack_bottom) + (1025 - (REQ).max_growth)))

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
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](              \
            ctx,                                                               \
            analysis,                                                          \
            stack_bottom,                                                      \
            stack_top + delta,                                                 \
            gas_remaining,                                                     \
            instr_ptr MONAD_VM_TBL_ARG);                                       \
    }                                                                          \
    while (false);

namespace monad::vm::interpreter
{
    using enum runtime::StatusCode;
    using enum compiler::EvmOpCode;

    // Aggregate requirements of a fused sequence, folded at compile time from the
    // same table `MONAD_VM_CHECK_AT` reads, so the two can never disagree.
    //
    //   gas           the sequence's total static gas
    //   min_required  entry height must be at least this, or some opcode underflows
    //   max_growth    entry height plus this must be at most 1024, or some opcode
    //                 overflows
    //
    // `min_required` is NOT derived from the net height change. SWAP16 moves the
    // height by zero and still needs 17 items, so each opcode's own `min_stack` is
    // folded against the running height. `max_growth` is the largest running height
    // the sequence reaches, and pops precede pushes within an opcode, so the peak of
    // an opcode is the larger of the heights either side of it.
    struct FusedRequirements
    {
        int64_t gas;
        int32_t min_required;
        int32_t max_growth;

        bool operator==(FusedRequirements const &) const = default;
    };

    // Declared and never defined, and deliberately not constexpr: calling it
    // inside a constant expression is a compile error. That is how a
    // dynamic-gas opcode is refused, the guest being built -fno-exceptions.
    void fused_requirements_rejects_dynamic_gas();

    template <Traits traits, compiler::EvmOpCode... Ops>
    consteval FusedRequirements fused_requirements()
    {
        FusedRequirements r{0, 0, 0};
        int32_t height = 0;
        for (auto const op : {Ops...}) {
            auto const ci = compiler::opcode_table<traits>[op];
            // A dynamic-gas opcode cannot be covered by one up-front test: its real
            // cost is not known here, so it has to stay a barrier and keep its own
            // check. Refuse to fold it rather than under-charge the sequence.
            if (ci.dynamic_gas) {
                fused_requirements_rejects_dynamic_gas();
            }
            r.gas += ci.min_gas;
            r.min_required =
                std::max(r.min_required, static_cast<int32_t>(ci.min_stack) - height);
            height = height - static_cast<int32_t>(ci.min_stack) +
                     static_cast<int32_t>(ci.stack_increase);
            r.max_growth = std::max(r.max_growth, height);
        }
        return r;
    }

#if defined(MONAD_VM_FUSE_JUMPDEST)
    // A taken jump lands on a JUMPDEST by construction -- jump_impl has just
    // validated it -- so the generic handler that follows can only charge its
    // 1 gas and step over it. Charging that gas here and landing one past it
    // removes a whole dispatch from every taken jump: 98,103 of the shipped
    // ziskethone guest's absorbed handler entries a block are exactly this.
    //
    // Charged AFTER validation, never before, so a bad destination still exits
    // Error without the JUMPDEST's gas having been taken. Reading code[jd + 1]
    // is what the generic path does anyway once it dispatches.
    [[gnu::always_inline]] inline uint8_t const *swallow_jumpdest(
        runtime::Context &ctx, uint8_t const *landing, int64_t &gas_remaining)
    {
        gas_remaining -= 1;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }
        return landing + 1;
    }
#endif

#if defined(MONAD_VM_FUSE_TESTJUMPI)
    // The tail shared by "<test> PUSH2 JUMPI": jump to the 16-bit immediate at
    // p[2..3] when taken, else fall past the five fused bytes. The test's
    // result never becomes a stack word -- it is a register the branch reads,
    // which is the round trip these triples exist to remove.
    [[gnu::always_inline]] inline uint8_t const *fused_branch(
        runtime::Context &ctx, Intercode const &analysis,
        uint8_t const *p, bool taken, int64_t &gas_remaining)
    {
        if (!taken) {
            return p + 5;
        }
        auto const dst = static_cast<size_t>(
            (static_cast<unsigned>(p[2]) << 8) | static_cast<unsigned>(p[3]));
        if (MONAD_UNLIKELY(!analysis.is_jumpdest(dst))) {
            ctx.exit(Error);
        }
        auto const *ip = analysis.code() + dst;
    #if defined(MONAD_VM_FUSE_JUMPDEST)
        ip = swallow_jumpdest(ctx, ip, gas_remaining);
    #endif
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
    template <uint8_t Opcode, Traits traits, typename... FnArgs>
    [[gnu::always_inline]] inline void checked_runtime_call(
        void (*f)(FnArgs...), runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t &gas_remaining, uint8_t const *)
    {
        check_requirements<Opcode, traits>(
            ctx, analysis, stack_bottom, stack_top, gas_remaining);
        call_runtime(f, ctx, stack_top, gas_remaining);
    }

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
        b = a + b;

        MONAD_VM_NEXT(ADD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        checked_runtime_call<MUL, traits>(
            runtime::mul,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
#if defined(MONAD_VM_FUSE_TESTJUMPI)
        // EQ PUSH2 <dst16> JUMPI -- "jump if equal". EQ pops two and pushes one,
        // so the PUSH2 that follows can never overflow the stack; only EQ's own
        // two-operand requirement needs checking.
        if (*(instr_ptr + 1) == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            static constexpr auto monad_vm_req =
                fused_requirements<traits, EQ, PUSH2, JUMPI>();
            if (MONAD_LIKELY(MONAD_VM_FUSED_OK(monad_vm_req))) {
                gas_remaining -= monad_vm_req.gas;
            }
            else {
                MONAD_VM_CHECK(EQ);
                // PUSH2's only stack test is overflow, and at SHIFT -1 it reads
                // `height - 1 > 1023`, i.e. `height > 1024`. The height is at
                // most 1024 on entry to any handler and EQ has already popped
                // two, so it cannot hold. Charge the gas.
                MONAD_DEBUG_ASSERT((stack_top - 1) - stack_bottom <= 1024);
                MONAD_VM_CHARGE(PUSH2);
                MONAD_VM_CHECK_AT(JUMPI, 0);
            }
            bool const monad_vm_taken = (*stack_top == *(stack_top - 1));
            instr_ptr = fused_branch(
                ctx, analysis, instr_ptr, monad_vm_taken, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx, analysis, stack_bottom, stack_top - 2, gas_remaining,
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
#if defined(MONAD_VM_FUSE_TESTJUMPI)
        // ISZERO PUSH2 <dst16> JUMPI -- "jump if zero", the commonest branch shape
        // a Solidity require() compiles to. Gate: two byte compares on every
        // ISZERO, which the fused triple has to earn back.
        if (*(instr_ptr + 1) == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            static constexpr auto monad_vm_req =
                fused_requirements<traits, ISZERO, PUSH2, JUMPI>();
            if (MONAD_LIKELY(MONAD_VM_FUSED_OK(monad_vm_req))) {
                gas_remaining -= monad_vm_req.gas;
            }
            else {
                MONAD_VM_CHECK(ISZERO);
                MONAD_VM_CHECK_AT(PUSH2, 0);
                MONAD_VM_CHECK_AT(JUMPI, 1);
            }
            bool const monad_vm_taken = !*stack_top;
            instr_ptr = fused_branch(
                ctx, analysis, instr_ptr, monad_vm_taken, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx, analysis, stack_bottom, stack_top - 1, gas_remaining,
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
        checked_runtime_call<SHA3, traits>(
            runtime::sha3<traits>,
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
        checked_runtime_call<CALLDATACOPY, traits>(
            runtime::calldatacopy<traits>,
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
        checked_runtime_call<CODECOPY, traits>(
            runtime::codecopy<traits>,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        checked_runtime_call<RETURNDATACOPY, traits>(
            runtime::returndatacopy<traits>,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BLOBBASEFEE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->blob_base_fee));

        MONAD_VM_NEXT(BLOBBASEFEE);
    }

    // Memory & Storage

    // MLOAD ends in a tail dispatch, so `ra` is live across the whole handler,
    // and two things on its path clobber it. The gas and stack exits are one,
    // and MONAD_VM_CHECK already answers those. The other is memory expansion,
    // a cold call that RETURNS: it rejoins the fast path, so the epilogue sits
    // on the joined path and no separate prologue can be placed.
    // Shrink-wrapping cannot fire and GCC spills the live arguments
    // unconditionally instead -- on block 25815100, six stack accesses and two
    // stack-pointer adjustments on each of 37,868 MLOADs.
    //
    // The twin takes the rest of the instruction with it, so the cold path no
    // longer rejoins. It must not repeat MONAD_VM_CHECK: the gas is charged and
    // the stack tested by the caller that tail-called it.
    //
    // Only the load direction. The same split on MSTORE is a regression:
    // `memory.size < *offset + 32` is the ordinary memory-growth test, not the
    // rare one, and MSTORE takes it on 19,626 of 47,194 executions -- it writes
    // where nothing has been written yet. MLOAD takes it 195 times, reading
    // what is already there. The rare event on the store side is capacity
    // growth, further in than this branch reaches.
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
        checked_runtime_call<MSTORE, traits>(
            runtime::mstore<traits>,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        checked_runtime_call<MSTORE8, traits>(
            runtime::mstore8<traits>,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        checked_runtime_call<MCOPY, traits>(
            runtime::mcopy<traits>,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
#if defined(MONAD_VM_FUSE_PUSH2JUMP)
        // PUSH2 <dst16> JUMP / JUMPI: the destination is a 16-bit immediate, so it
        // never becomes a 256-bit stack word that the jump then compares against
        // size_t and pops. JUMP and JUMPI are 0x56 and 0x57, so the gate on every
        // PUSH2 is a subtract and an unsigned compare.
        //
        // Order is the unfused order: PUSH2's gas and room, then the jump's gas
        // and its operands, then destination validation -- a bad destination still
        // exits Error with the jump's gas already charged, as it does today.
        if constexpr (N == 2) {
            auto const monad_vm_op2 = *(instr_ptr + 3);
            if (static_cast<unsigned>(monad_vm_op2 -
                                      static_cast<std::uint8_t>(JUMP)) <= 1u) {
                // Reading the destination immediate is pure, so it moves above
                // the checks: the aggregate has to know which follower it is
                // before it can test the sequence, and PUSH2 and JUMPI do not
                // aggregate to the same requirements as PUSH2 and JUMP.
                auto const monad_vm_dst = static_cast<size_t>(
                    (static_cast<unsigned>(*(instr_ptr + 1)) << 8) |
                    static_cast<unsigned>(*(instr_ptr + 2)));
                if (monad_vm_op2 == static_cast<std::uint8_t>(JUMP)) {
                    static constexpr auto monad_vm_req =
                        fused_requirements<traits, PUSH2, JUMP>();
                    if (MONAD_LIKELY(MONAD_VM_FUSED_OK(monad_vm_req))) {
                        gas_remaining -= monad_vm_req.gas;
                    }
                    else {
                        MONAD_VM_CHECK(PUSH2);
                        // JUMP needs one operand and the PUSH2 supplies it, so
                        // at SHIFT 1 the test reads `height + 1 < 1`, i.e.
                        // `height < 0`. Charge the gas and skip it.
                        MONAD_DEBUG_ASSERT(stack_top >= stack_bottom);
                        MONAD_VM_CHARGE(JUMP);
                    }
                    if (MONAD_UNLIKELY(!analysis.is_jumpdest(monad_vm_dst))) {
                        ctx.exit(Error);
                    }
                    auto const *monad_vm_ip = analysis.code() + monad_vm_dst;
    #if defined(MONAD_VM_FUSE_JUMPDEST)
                    monad_vm_ip =
                        swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
    #endif
                    instr_ptr = monad_vm_ip;
                    MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                        ctx, analysis, stack_bottom, stack_top, gas_remaining,
                        instr_ptr MONAD_VM_TBL_ARG);
                }
                static constexpr auto monad_vm_reqi =
                    fused_requirements<traits, PUSH2, JUMPI>();
                if (MONAD_LIKELY(MONAD_VM_FUSED_OK(monad_vm_reqi))) {
                    gas_remaining -= monad_vm_reqi.gas;
                }
                else {
                    MONAD_VM_CHECK(PUSH2);
                    MONAD_VM_CHECK_AT(JUMPI, 1);
                }
                // The condition is the word under the immediate, i.e. the stack top
                // the handler was entered with.
                if (*stack_top) {
                    if (MONAD_UNLIKELY(!analysis.is_jumpdest(monad_vm_dst))) {
                        ctx.exit(Error);
                    }
                    auto const *monad_vm_ip = analysis.code() + monad_vm_dst;
    #if defined(MONAD_VM_FUSE_JUMPDEST)
                    monad_vm_ip =
                        swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
    #endif
                    instr_ptr = monad_vm_ip;
                    MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                        ctx, analysis, stack_bottom, stack_top - 1,
                        gas_remaining, instr_ptr MONAD_VM_TBL_ARG);
                }
                MONAD_VM_FUSED_NEXT(4, -1);
            }
        }
#endif
#if defined(MONAD_VM_FUSE_PUSH1OP)
        // PUSH1 <imm> followed by a binary operator whose other operand is the
        // stack top: the immediate never reaches memory. Unfused it is written as
        // a 256-bit word at stack_top + 1 and read straight back by the operator,
        // which is the round trip this removes -- the saved dispatch is the
        // smaller half.
        //
        // The operators below all take top_two(stack_top) as (a, b) and write b,
        // so with the immediate standing in for a, the result lands in *stack_top
        // and the pair's net stack movement is zero.
        //
        // Check order is the unfused order: PUSH1's gas and room for one more word
        // first, then the operator's gas and its two-operand requirement against
        // the stack PUSH1 leaves. Reading instr_ptr[2] is safe for the same reason
        // the generic path may read it: the code is padded.
        if constexpr (N == 1) {
            // The gate runs on EVERY PUSH1 and pays off on the fraction that match,
            // so its cost is the whole design. A chain of four byte compares was
            // measured at +1.4 % -- eight instructions on every push to save a
            // dispatch on one in seven. A bitmap is four: compare, shift, and,
            // branch. ADD, SHL, SHR and SAR are opcodes 1, 27, 28 and 29, so a
            // 64-bit mask covers them with room to spare.
            constexpr std::uint64_t monad_vm_fuse_mask =
                (1ull << static_cast<unsigned>(ADD)) |
                (1ull << static_cast<unsigned>(SHL)) |
                (1ull << static_cast<unsigned>(SHR)) |
                (1ull << static_cast<unsigned>(SAR));
            // PUSH1+PUSH1 and PUSH1+DUP2, which ziskethone also fuses, are left
            // out: their followers are opcodes 0x60 and 0x81, outside a 64-bit
            // mask, and widening the gate is what the chain-of-compares version
            // measured at +1.4 % against this one's -0.9 %. Both write their
            // operands to memory anyway, so they save a dispatch and not a round
            // trip -- the smaller half of what the four below return.
            auto const monad_vm_op2 = *(instr_ptr + 2);
            if (monad_vm_op2 < 64 &&
                ((monad_vm_fuse_mask >> monad_vm_op2) & 1)) {
                // All four followers in the mask pop two, push one and cost 3,
                // so one set of requirements covers the whole branch and the
                // fallback needs one follower check rather than one per arm.
                // The assertion is what keeps that true if the mask grows.
                static constexpr auto monad_vm_req =
                    fused_requirements<traits, PUSH1, ADD>();
                static_assert(
                    monad_vm_req == fused_requirements<traits, PUSH1, SHL>() &&
                    monad_vm_req == fused_requirements<traits, PUSH1, SHR>() &&
                    monad_vm_req == fused_requirements<traits, PUSH1, SAR>(),
                    "PUSH1 fusion mask holds followers with unequal "
                    "requirements; aggregate them per follower");
                if (MONAD_LIKELY(MONAD_VM_FUSED_OK(monad_vm_req))) {
                    gas_remaining -= monad_vm_req.gas;
                }
                else {
                    MONAD_VM_CHECK(PUSH1);
                    MONAD_VM_CHECK_AT(ADD, 1);
                }
                uint256_t const monad_vm_imm{*(instr_ptr + 1)};
                if (monad_vm_op2 == static_cast<std::uint8_t>(ADD)) {
                    *stack_top = monad_vm_imm + *stack_top;
                }
                else if (monad_vm_op2 == static_cast<std::uint8_t>(SHL)) {
                    *stack_top <<= monad_vm_imm;
                }
                else if (monad_vm_op2 == static_cast<std::uint8_t>(SHR)) {
                    *stack_top >>= monad_vm_imm;
                }
                else {
                    *stack_top = sar(monad_vm_imm, *stack_top);
                }
                MONAD_VM_FUSED_NEXT(3, 0);
            }
        }
#endif
        push_impl<N, traits>::push(
            ctx, analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);

        MONAD_VM_NEXT_PUSH(PUSH0 + N);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(POP);
#if defined(MONAD_VM_FUSE_POPPOP)
        // Two pops move the stack pointer twice and dispatch twice; the second
        // dispatch is all that is saved, so the peek has to be cheap -- one byte
        // compare against a constant. Checks stay in order: this POP's gas and
        // stack are already charged above, the next one's are charged against the
        // stack this one leaves, so an out-of-gas on the second halts exactly
        // where the unfused pair would.
        if (*(instr_ptr + 1) == static_cast<std::uint8_t>(POP)) {
            MONAD_VM_CHECK_AT(POP, -1);
            MONAD_VM_FUSED_NEXT(2, -2);
        }
#endif
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

#if defined(MONAD_ZKVM_SP1)
        // rv32: the trivial 32-byte uint256 copies lower to memcpy CALLS
        // (~95 k per block across SWAP1-3 alone, measured by the memcpy
        // return-address histogram); exchange the four lanes in place.
        auto *const a = reinterpret_cast<uint64_t *>(stack_top);
        auto *const b = reinterpret_cast<uint64_t *>(stack_top - N);
        for (int i = 0; i < 4; ++i) {
            uint64_t const t = a[i];
            a[i] = b[i];
            b[i] = t;
        }
#else
        // A plain temporary, not the AVX type. Exchanging two 32-byte words needs three copies --
        // save, move down, restore -- and that is what this emits. The round trip through to_avx()
        // and back emitted FOUR: measured on block 25815100, every one of the sixteen swap<N>
        // instantiations ran exactly 4.00 dma_xmemcpy an entry against dup<N>'s 1.00, and the extra
        // one is frame-slot to frame-slot inside our own stack, the AVX conversion having
        // materialised two 32-byte slots instead of one.
        //
        // NOT the lane exchange the SP1 arm uses: that was measured on ZisK at +0.9-1.8 % steps and
        // is refuted (FINDINGS 161). Four 8-byte pairs cost more here than one 32-byte DMA copy,
        // which is exactly the opposite of the rv32 case above.
        uint256_t const top = *stack_top;
        *stack_top = *(stack_top - N);
        *(stack_top - N) = top;
#endif

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
        int64_t gas_remaining, uint8_t const * MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(JUMP);
        auto const &target = pop(stack_top);
        auto const *new_ip = jump_impl(ctx, analysis, target);
#if defined(MONAD_VM_FUSE_JUMPDEST)
        new_ip = swallow_jumpdest(ctx, new_ip, gas_remaining);
#endif

        if constexpr (debug_enabled) {
            trace(analysis, gas_remaining, new_ip);
        }
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
            ctx, analysis, stack_bottom, stack_top, gas_remaining,
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
#if defined(MONAD_VM_FUSE_JUMPDEST)
            new_ip = swallow_jumpdest(ctx, new_ip, gas_remaining);
#endif
            if constexpr (debug_enabled) {
                trace(analysis, gas_remaining, new_ip);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
                ctx, analysis, stack_bottom, stack_top, gas_remaining,
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
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
        int64_t gas_remaining, uint8_t const * MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        MONAD_VM_CHECK(RETURN);
        return_impl(Success, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &ctx, Intercode const &analysis,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const * MONAD_VM_TBL_TYPE)
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
        uint256_t const *const stack_bottom, uint256_t *const stack_top,
        int64_t const gas_remaining, uint8_t const * MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(ctx, stack_bottom, stack_top, analysis.size());
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Success);
    }

    MONAD_VM_INSTRUCTION_CALL inline void invalid(
        runtime::Context &ctx, Intercode const &, uint256_t const *,
        uint256_t *, int64_t const gas_remaining, uint8_t const * MONAD_VM_TBL_TYPE)
    {
        ctx.gas_remaining = gas_remaining;
        ctx.exit(Error);
    }
}

#undef MONAD_VM_MUST_TAIL
#undef MONAD_VM_NEXT
#undef MONAD_VM_NEXT_PUSH
