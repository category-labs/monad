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
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/runtime.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/utils/debug.hpp>

#include <evmc/evmc.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <type_traits>

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
// Hide P's new value from the optimiser, so that what follows reads through
// it rather than through the old one. The old value then dies here and its
// register can take the new one; otherwise both stay live, and gcc keeps a
// copy of one of them from the handler's first instruction on.
    #define MONAD_VM_LAUNDER(P) asm("" : "+r"(P))
#else
    #define MONAD_VM_LAUNDER(P)
#endif

namespace monad::vm::interpreter
{
    // ctx through MONAD_VM_LAUNDER, for a handler whose other values gcc would
    // otherwise place in a0: laundered, ctx stays there, and the handler no
    // longer saves it away at its first instruction and restores it before
    // the dispatch.
    [[gnu::always_inline]] inline runtime::Context &
    held_in_a0(runtime::Context &ctx) noexcept
    {
        auto *p = &ctx;
        MONAD_VM_LAUNDER(p);
        return *p;
    }

#if defined(MONAD_ZKVM_ZISK)
    // A revision's handlers, one to a slot of 1 << slot_shift bytes in opcode
    // order: execute.cpp compiles each handler into its slot, and the linker
    // script that zkvm/build-support writes places the slots. A handler's
    // address is the base plus its opcode's offset, so the dispatch is one
    // read and one step shorter than a table's.
    inline constexpr size_t slot_shift = 12;

    // A slot holds six copies of the opcode's handler, one per lag L: entered
    // with instr_ptr L bytes ahead of a5, so that an opcode of N bytes
    // dispatches to its follower's copy L + N without stepping a5 while
    // L + N < lag_count (MONAD_VM_DISPATCH). lag_offset(L) is where the copy's
    // handler sits from the base the handlers carry: within a jalr's reach,
    // heads included. A handler too large for a copy is compiled once, past
    // the slots, and its copies jump there (execute.cpp).
    inline constexpr unsigned lag_count = 6;

    consteval int lag_offset(unsigned const lag) noexcept
    {
        constexpr int at[lag_count] = {0, 680, 1360, 2044, -1368, -684};
        return at[lag];
    }

    // The traits of a copy: the revision's, and the lag. SENDS is whether the
    // copy's dispatches may go to the lagging copies (lag_dispatch); a copy
    // whose handler keeps a frame must not.
    template <Traits T, unsigned L, bool SENDS = true>
    struct Lagged : T
    {
        static constexpr unsigned lag = L;
    };

    template <class T>
    struct LagOf
    {
        static constexpr unsigned value = 0;
        static constexpr bool sends = true;
        using base = T;
    };

    template <Traits T, unsigned L, bool SENDS>
    struct LagOf<Lagged<T, L, SENDS>>
    {
        static constexpr unsigned value = L;
        static constexpr bool sends = SENDS;
        using base = T;
    };

    template <class T>
    inline constexpr unsigned lag_of = LagOf<T>::value;

    // The same traits, their dispatches gcc's: for a handler or a twin that
    // keeps a frame on a path to its dispatch, which a jump made by hand
    // would leave open (gcc emits an epilogue before its own tail calls
    // only).
    template <class T>
    using quiet_traits =
        Lagged<typename LagOf<T>::base, LagOf<T>::value, false>;

    // The opcodes whose handlers keep a frame on such a path, read off the
    // objdump: the runtime's calls, the environment's, and the arithmetic
    // that calls out. The official-build audit fails an ELF in which a jump
    // made by hand still leaves with a frame open (check_hand_made_jumps).
    consteval bool keeps_frame(uint8_t const op) noexcept
    {
        using enum compiler::EvmOpCode;
        constexpr uint8_t ops[] = {MUL,          DIV,          SDIV,
                                   MOD,          SMOD,         ADDMOD,
                                   MULMOD,       EXP,          BYTE,
                                   SAR,          SHA3,         ADDRESS,
                                   BALANCE,      ORIGIN,       CALLER,
                                   CALLDATALOAD, CALLDATACOPY, CODECOPY,
                                   EXTCODESIZE,  EXTCODECOPY,  RETURNDATACOPY,
                                   EXTCODEHASH,  BLOCKHASH,    COINBASE,
                                   SELFBALANCE,  BLOBHASH,     MSTORE8,
                                   SLOAD,        SSTORE,       TLOAD,
                                   TSTORE,       MCOPY,        LOG0,
                                   LOG1,         LOG2,         LOG3,
                                   LOG4,         CREATE,       CALL,
                                   CALLCODE,     DELEGATECALL, CREATE2,
                                   STATICCALL};
        for (uint8_t const o : ops) {
            if (o == op) {
                return true;
            }
        }
        return false;
    }

    // The followers whose PUSH1 pair keeps a frame on such a path.
    consteval bool pair_keeps_frame(uint8_t const op) noexcept
    {
        using enum compiler::EvmOpCode;
        return op == SHR || op == SAR || op == CALLDATALOAD;
    }

    // The revision's traits, for what is instantiated or specialised on them
    // alone: the runtime's functions, the storage cost tables.
    template <class T>
    using base_traits = typename LagOf<T>::base;

    // Where copy 0's handler sits in its slot, after copies 4 and 5 and its
    // own heads: the base the handlers carry points there, at opcode 0's
    // copy 0, and the other copies are lag_offset away.
    inline constexpr size_t slot_lead = 1580;

    // Where they land, before each copy's handler: PUSH1's head pushes its
    // immediate and falls into the handler; PUSH2's makes its stack test,
    // reads its immediate and jumps to the push in PUSH1's. In copy R, PUSH1's
    // head takes a PUSH1 one (R + 4) % 6 bytes behind, PUSH2's a PUSH2
    // (R + 3) % 6 behind; PUSH1's steps a5 in copies 0 and 1 only, and is four
    // bytes shorter in the others.
    consteval int head_back(unsigned const copy, unsigned const n) noexcept
    {
        return (n == 1 ? 32 : 56) - (copy >= 2 ? 4 : 0);
    }

    // What MONAD_VM_LEAD_DISPATCH takes for a PUSH<n> LAG bytes behind.
    consteval int lead_offset(unsigned const lag, unsigned const n) noexcept
    {
        unsigned const copy = (lag + n + 1) % lag_count;
        return head_back(copy, n) - lag_offset(copy);
    }

    // Where SWAP1 lands in every copy: its head comes before PUSH2's,
    // swap1_back bytes before the handler. In copy R it takes a SWAP1
    // (R + 5) % 6 bytes behind, stepping a5 by 6 in copy 0.
    inline constexpr int swap1_back = 104;

    // What MONAD_VM_LEAD_DISPATCH takes for a SWAP1 LAG bytes behind.
    consteval int swap1_offset(unsigned const lag) noexcept
    {
        unsigned const copy = (lag + 1) % lag_count;
        return swap1_back - lag_offset(copy);
    }

    // The head of DUP2 to DUP16 comes before SWAP1's, dup_back bytes before
    // the handler, and takes a DUPn as SWAP1's takes a SWAP1, the address of
    // the word it copies in a7.
    inline constexpr int dup_back = 144;

    // What MONAD_VM_LEAD_DISPATCH_SRC takes for a DUPn LAG bytes behind.
    consteval int dup_offset(unsigned const lag) noexcept
    {
        unsigned const copy = (lag + 1) % lag_count;
        return dup_back - lag_offset(copy);
    }

    // The head of SWAP2 to SWAP16 comes before the DUPs', swapn_back bytes
    // before the handler, the address of the word the top swaps with in a7.
    inline constexpr int swapn_back = 184;

    // What MONAD_VM_LEAD_DISPATCH_SRC takes for a SWAPn LAG bytes behind.
    consteval int swapn_offset(unsigned const lag) noexcept
    {
        unsigned const copy = (lag + 1) % lag_count;
        return swapn_back - lag_offset(copy);
    }

    // The head of LT, GT, SLT, SGT, EQ and ISZERO comes before SWAPn's,
    // bool_back bytes before the handler, the result in a7 and its slot at
    // the top, not yet written.
    inline constexpr int bool_back = 212;

    // What MONAD_VM_LEAD_DISPATCH_BIT takes for a comparison LAG bytes
    // behind.
    consteval int bool_offset(unsigned const lag) noexcept
    {
        unsigned const copy = (lag + 1) % lag_count;
        return bool_back - lag_offset(copy);
    }

    // A tail call to a head in NEXT_OPCODE's slot, OFFSET bytes before its
    // handler, made by hand for the jump to take -OFFSET as its immediate:
    // through a function pointer gcc forms the head's address with an addi of
    // its own. The arguments are where the call would put them.
    #define MONAD_VM_LEAD_DISPATCH(OFFSET, NEXT_OPCODE, TOP, GAS, IP)          \
        do {                                                                   \
            auto const monad_vm_head =                                         \
                reinterpret_cast<uintptr_t>(itbl) +                            \
                (static_cast<uintptr_t>(NEXT_OPCODE) << slot_shift);           \
            register runtime::Context *monad_vm_a0 asm("a0") = &ctx;           \
            register uint256_t const *monad_vm_a1 asm("a1") =                  \
                MONAD_VM_ANALYSIS_ARG;                                         \
            register uint256_t const *monad_vm_a2 asm("a2") = stack_bottom;    \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP);                 \
            register int64_t monad_vm_a4 asm("a4") = (GAS);                    \
            register uint8_t const *monad_vm_a5 asm("a5") = (IP);              \
            register void const *monad_vm_a6 asm("a6") = itbl;                 \
            asm volatile("jalr zero, %[off](%[head])"                          \
                         :                                                     \
                         : [head] "r"(monad_vm_head),                          \
                           [off] "i"(-static_cast<int>(OFFSET)),               \
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

    // MONAD_VM_LEAD_DISPATCH with SRC in a7, for the head and the pairs past
    // it.
    #define MONAD_VM_LEAD_DISPATCH_SRC(OFFSET, NEXT_OPCODE, TOP, GAS, IP, SRC) \
        do {                                                                   \
            auto const monad_vm_head =                                         \
                reinterpret_cast<uintptr_t>(itbl) +                            \
                (static_cast<uintptr_t>(NEXT_OPCODE) << slot_shift);           \
            register runtime::Context *monad_vm_a0 asm("a0") = &ctx;           \
            register uint256_t const *monad_vm_a1 asm("a1") =                  \
                MONAD_VM_ANALYSIS_ARG;                                         \
            register uint256_t const *monad_vm_a2 asm("a2") = stack_bottom;    \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP);                 \
            register int64_t monad_vm_a4 asm("a4") = (GAS);                    \
            register uint8_t const *monad_vm_a5 asm("a5") = (IP);              \
            register void const *monad_vm_a6 asm("a6") = itbl;                 \
            register uint256_t const *monad_vm_a7 asm("a7") = (SRC);           \
            asm volatile("jalr zero, %[off](%[head])"                          \
                         :                                                     \
                         : [head] "r"(monad_vm_head),                          \
                           [off] "i"(-static_cast<int>(OFFSET)),               \
                           "r"(monad_vm_a0),                                   \
                           "r"(monad_vm_a1),                                   \
                           "r"(monad_vm_a2),                                   \
                           "r"(monad_vm_a3),                                   \
                           "r"(monad_vm_a4),                                   \
                           "r"(monad_vm_a5),                                   \
                           "r"(monad_vm_a6),                                   \
                           "r"(monad_vm_a7)                                    \
                         : "memory");                                          \
            __builtin_unreachable();                                           \
        }                                                                      \
        while (false)

    // MONAD_VM_LEAD_DISPATCH with BIT, a comparison's result, in a7.
    #define MONAD_VM_LEAD_DISPATCH_BIT(OFFSET, NEXT_OPCODE, TOP, GAS, IP, BIT) \
        do {                                                                   \
            auto const monad_vm_head =                                         \
                reinterpret_cast<uintptr_t>(itbl) +                            \
                (static_cast<uintptr_t>(NEXT_OPCODE) << slot_shift);           \
            register runtime::Context *monad_vm_a0 asm("a0") = &ctx;           \
            register uint256_t const *monad_vm_a1 asm("a1") =                  \
                MONAD_VM_ANALYSIS_ARG;                                         \
            register uint256_t const *monad_vm_a2 asm("a2") = stack_bottom;    \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP);                 \
            register int64_t monad_vm_a4 asm("a4") = (GAS);                    \
            register uint8_t const *monad_vm_a5 asm("a5") = (IP);              \
            register void const *monad_vm_a6 asm("a6") = itbl;                 \
            register uint64_t monad_vm_a7 asm("a7") = (BIT);                   \
            asm volatile("jalr zero, %[off](%[head])"                          \
                         :                                                     \
                         : [head] "r"(monad_vm_head),                          \
                           [off] "i"(-static_cast<int>(OFFSET)),               \
                           "r"(monad_vm_a0),                                   \
                           "r"(monad_vm_a1),                                   \
                           "r"(monad_vm_a2),                                   \
                           "r"(monad_vm_a3),                                   \
                           "r"(monad_vm_a4),                                   \
                           "r"(monad_vm_a5),                                   \
                           "r"(monad_vm_a6),                                   \
                           "r"(monad_vm_a7)                                    \
                         : "memory");                                          \
            __builtin_unreachable();                                           \
        }                                                                      \
        while (false)

    // The tail call to NEXT_OPCODE's copy TO, lag_offset(TO) from its
    // handler, by hand as MONAD_VM_LEAD_DISPATCH: IP is instr_ptr TO bytes
    // before the opcode.
    #define MONAD_VM_LAG_DISPATCH(TO, NEXT_OPCODE, TOP, GAS, IP)               \
        do {                                                                   \
            auto const monad_vm_head =                                         \
                reinterpret_cast<uintptr_t>(itbl) +                            \
                (static_cast<uintptr_t>(NEXT_OPCODE) << slot_shift);           \
            register runtime::Context *monad_vm_a0 asm("a0") = &ctx;           \
            register uint256_t const *monad_vm_a1 asm("a1") =                  \
                MONAD_VM_ANALYSIS_ARG;                                         \
            register uint256_t const *monad_vm_a2 asm("a2") = stack_bottom;    \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP);                 \
            register int64_t monad_vm_a4 asm("a4") = (GAS);                    \
            register uint8_t const *monad_vm_a5 asm("a5") = (IP);              \
            register void const *monad_vm_a6 asm("a6") = itbl;                 \
            asm volatile("jalr zero, %[off](%[head])"                          \
                         :                                                     \
                         : [head] "r"(monad_vm_head),                          \
                           [off] "i"(lag_offset(TO)),                          \
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
        std::is_same_v<base_traits<traits>, EvmTraits<traits::evm_rev()>> &&
        traits::evm_rev() >= MONAD_ETH_BERLIN &&
        traits::evm_rev() <= MONAD_ETH_AMSTERDAM;

    // Whether a handler's dispatches go to its follower's lagging copies
    // (MONAD_VM_LAG_TRY): all but those of a handler that keeps a frame.
    template <Traits traits>
    inline constexpr bool lag_dispatch =
        has_slots<traits> && LagOf<traits>::sends;

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
    dispatch_table(void const *const itbl) noexcept
    {
        if constexpr (has_slots<traits>) {
            return SlotTable{itbl};
        }
        else {
            return static_cast<InstrEval const *>(itbl);
        }
    }
#else
    // One copy of each handler: its traits are the revision's.
    template <class T>
    using base_traits = T;

    template <class T>
    using quiet_traits = T;
#endif
}

// A twin a handler tail-calls takes instr_ptr as the handler's copy has it in
// a5, the copy's lag behind, and steps it on itself: the copy passes a5 on as
// it came.
#if defined(MONAD_ZKVM_ZISK)
    #define MONAD_VM_AS_CALLED(IP)                                             \
        ((IP) - ::monad::vm::interpreter::lag_of<traits>)
    #define MONAD_VM_TWIN_ENTRY()                                              \
        (instr_ptr += ::monad::vm::interpreter::lag_of<traits>)
    // instr_ptr held in a5 as it came, not the lag on.
    #define MONAD_VM_LAUNDER_AS_CALLED(IP)                                     \
        do {                                                                   \
            auto *monad_vm_raw = MONAD_VM_AS_CALLED(IP);                       \
            MONAD_VM_LAUNDER(monad_vm_raw);                                    \
            (IP) = monad_vm_raw + ::monad::vm::interpreter::lag_of<traits>;    \
        }                                                                      \
        while (false)
#else
    #define MONAD_VM_AS_CALLED(IP) (IP)
    #define MONAD_VM_TWIN_ENTRY() ((void)0)
    #define MONAD_VM_LAUNDER_AS_CALLED(IP) MONAD_VM_LAUNDER(IP)
#endif

// Evaluate NEXT_OPCODE after advancing instr_ptr; it may be *instr_ptr.
#if defined(MONAD_ZKVM_ZISK)
    // Past N bytes, to the follower's copy lag + N while there is one, a5
    // where it was.
    #define MONAD_VM_LAG_TRY(N, NBYTES, DELTA, NEXT_OPCODE)                    \
        if constexpr (                                                         \
            ::monad::vm::interpreter::lag_of<traits> + (N) <                   \
            ::monad::vm::interpreter::lag_count) {                             \
            if ((NBYTES) == (N)) {                                             \
                instr_ptr += (N);                                              \
                if constexpr (debug_enabled) {                                 \
                    trace(MONAD_VM_ANALYSIS, gas_remaining, instr_ptr);        \
                }                                                              \
                MONAD_VM_LAG_DISPATCH(                                         \
                    ::monad::vm::interpreter::lag_of<traits> + (N),            \
                    (NEXT_OPCODE),                                             \
                    stack_top + (DELTA),                                       \
                    gas_remaining,                                             \
                    instr_ptr -                                                \
                        (::monad::vm::interpreter::lag_of<traits> + (N)));     \
            }                                                                  \
        }
    // Otherwise to its copy 0, a5 stepped.
    #define MONAD_VM_DISPATCH(NBYTES, DELTA, NEXT_OPCODE)                      \
        do {                                                                   \
            if constexpr (::monad::vm::interpreter::lag_dispatch<traits>) {    \
                MONAD_VM_LAG_TRY(1, NBYTES, DELTA, NEXT_OPCODE);               \
                MONAD_VM_LAG_TRY(2, NBYTES, DELTA, NEXT_OPCODE);               \
                MONAD_VM_LAG_TRY(3, NBYTES, DELTA, NEXT_OPCODE);               \
                MONAD_VM_LAG_TRY(4, NBYTES, DELTA, NEXT_OPCODE);               \
                MONAD_VM_LAG_TRY(5, NBYTES, DELTA, NEXT_OPCODE);               \
            }                                                                  \
            {                                                                  \
                instr_ptr += (NBYTES);                                         \
                MONAD_VM_LAUNDER(instr_ptr);                                   \
                if constexpr (debug_enabled) {                                 \
                    trace(MONAD_VM_ANALYSIS, gas_remaining, instr_ptr);        \
                }                                                              \
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[(NEXT_OPCODE)](   \
                    ctx,                                                       \
                    MONAD_VM_ANALYSIS_ARG,                                     \
                    stack_bottom,                                              \
                    stack_top + (DELTA),                                       \
                    gas_remaining,                                             \
                    instr_ptr MONAD_VM_TBL_ARG);                               \
            }                                                                  \
        }                                                                      \
        while (false)
#else
    #define MONAD_VM_DISPATCH(NBYTES, DELTA, NEXT_OPCODE)                      \
        do {                                                                   \
            instr_ptr += (NBYTES);                                             \
            MONAD_VM_LAUNDER(instr_ptr);                                       \
            if constexpr (debug_enabled) {                                     \
                trace(MONAD_VM_ANALYSIS, gas_remaining, instr_ptr);            \
            }                                                                  \
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[(NEXT_OPCODE)](       \
                ctx,                                                           \
                MONAD_VM_ANALYSIS_ARG,                                         \
                stack_bottom,                                                  \
                stack_top + (DELTA),                                           \
                gas_remaining,                                                 \
                instr_ptr MONAD_VM_TBL_ARG);                                   \
        }                                                                      \
        while (false)
#endif

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

#if defined(MONAD_ZKVM_ZISK)
// MONAD_VM_CHECK with one test leaving through an exit of its own, for a
// handler whose other exits include an equal call: DUP's two stack tests both
// leave with Error, and MLOAD's and MSTORE's gas and offset tests both with
// OutOfGas. gcc merges equal exit calls into one block, and a block reached
// from two tests costs a copy of ctx on every execution. Not for every
// handler: PUSH1 pays two instructions an execution for the same change.
    #define MONAD_VM_EXIT_OWN_OUT_OF_GAS(CODE)                                 \
        MONAD_VM_MUST_TAIL return ::monad::vm::interpreter::exit_out_of_gas(ctx)
    #define MONAD_VM_EXIT_OWN_OVERFLOW(CODE)                                   \
        MONAD_VM_MUST_TAIL return ::monad::vm::interpreter::exit_stack_overflow( \
            ctx)
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
// Reuse the cached stack limit; the adjustment folds to zero for growth 1.
#define MONAD_VM_FUSED_CHARGE(REQ)                                             \
    (::monad::vm::interpreter::charge_gas(gas_remaining, (REQ).gas) &&         \
     ::monad::vm::interpreter::stack_holds<(REQ).min_required>(                \
         stack_top, stack_bottom) &&                                           \
     ((REQ).max_growth == 0 ||                                                 \
      (stack_top) < MONAD_VM_STACK_LIMIT + (1 - (REQ).max_growth)))

// MONAD_VM_FUSED_CHARGE for a sequence of pure opcodes (gas_tested), or of
// pure opcodes and a JUMPI: on ZisK its charge leaves the sign of the count to
// the next checkpoint, which for a taken JUMPI is the JUMPDEST it lands on
// (swallow_jumpdest), and otherwise the straight line after it.
#if defined(MONAD_ZKVM_ZISK)
    #define MONAD_VM_FUSED_CHARGE_PURE(REQ)                                    \
        ((gas_remaining -= (REQ).gas, true) &&                                 \
         ::monad::vm::interpreter::stack_holds<(REQ).min_required>(            \
             stack_top, stack_bottom) &&                                       \
         ((REQ).max_growth == 0 ||                                             \
          (stack_top) < MONAD_VM_STACK_LIMIT + (1 - (REQ).max_growth)))
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
        FusedRequirements r{0, 0, 0};
        int32_t height = 0;
        for (auto const op : {Ops...}) {
            auto const ci = compiler::opcode_table<traits>[op];
            // Dynamic gas cannot be included in this static total:
            // triggers compilation error
            if (ci.dynamic_gas) {
                fused_requirements_rejects_dynamic_gas();
            }
            r.gas += ci.min_gas;
            r.min_required =
                // - height because some previous opcode can free space, like
                // for the sequence PUSH2 + JUMPI (2 elements needed, one
                // provided by PUSH2)
                std::max(
                    r.min_required,
                    static_cast<int32_t>(ci.min_stack) - height);
            height = height - static_cast<int32_t>(ci.min_stack) +
                     static_cast<int32_t>(ci.stack_increase);
            r.max_growth = std::max(r.max_growth, height);
        }
        return r;
    }

#if defined(MONAD_ZKVM_ZISK)
    // The static gas of a sequence, a dynamic-cost opcode's at its minimum:
    // for a caller that charges the dynamic part itself.
    template <Traits traits, compiler::EvmOpCode... Ops>
    consteval int64_t static_gas()
    {
        return (
            static_cast<int64_t>(compiler::opcode_table<traits>[Ops].min_gas) +
            ...);
    }

    // Charge gas and tell whether it was covered. The sign of what is left is
    // one test; gcc would compare the gas before the charge instead, against a
    // constant it must load first.
    [[gnu::always_inline]] inline bool
    charge_gas(int64_t &gas_remaining, int64_t const gas)
    {
        gas_remaining -= gas;
        MONAD_VM_LAUNDER(gas_remaining);
        return gas_remaining >= 0;
    }

    // x >> k and x << k in place, for k under 256: one arm per whole words
    // of the shift, whose few temporaries leave the handler without the frame
    // the general shift needs for its run-time word index. A word's bits that
    // cross into its neighbour move in two shifts, (w << 1) << (63 - b) and
    // (w >> 1) >> (63 - b), which are also right for b = 0.
    [[gnu::always_inline]] inline void
    shr_in_place(uint256_t &x, uint64_t const k) noexcept
    {
        unsigned const b = static_cast<unsigned>(k & 63);
        auto const down = [b](uint64_t const w) {
            return (w << 1) << (63 - b);
        };
        switch (k >> 6) {
        case 0: {
            uint64_t const x0 = x[0], x1 = x[1], x2 = x[2], x3 = x[3];
            x[0] = (x0 >> b) | down(x1);
            x[1] = (x1 >> b) | down(x2);
            x[2] = (x2 >> b) | down(x3);
            x[3] = x3 >> b;
            break;
        }
        case 1: {
            uint64_t const x1 = x[1], x2 = x[2], x3 = x[3];
            x[0] = (x1 >> b) | down(x2);
            x[1] = (x2 >> b) | down(x3);
            x[2] = x3 >> b;
            x[3] = 0;
            break;
        }
        case 2: {
            uint64_t const x2 = x[2], x3 = x[3];
            x[0] = (x2 >> b) | down(x3);
            x[1] = x3 >> b;
            x[2] = 0;
            x[3] = 0;
            break;
        }
        default: {
            uint64_t const x3 = x[3];
            x[0] = x3 >> b;
            x[1] = 0;
            x[2] = 0;
            x[3] = 0;
            break;
        }
        }
    }

    [[gnu::always_inline]] inline void
    shl_in_place(uint256_t &x, uint64_t const k) noexcept
    {
        unsigned const b = static_cast<unsigned>(k & 63);
        auto const up = [b](uint64_t const w) { return (w >> 1) >> (63 - b); };
        switch (k >> 6) {
        case 0: {
            uint64_t const x0 = x[0], x1 = x[1], x2 = x[2], x3 = x[3];
            x[3] = (x3 << b) | up(x2);
            x[2] = (x2 << b) | up(x1);
            x[1] = (x1 << b) | up(x0);
            x[0] = x0 << b;
            break;
        }
        case 1: {
            uint64_t const x0 = x[0], x1 = x[1], x2 = x[2];
            x[3] = (x2 << b) | up(x1);
            x[2] = (x1 << b) | up(x0);
            x[1] = x0 << b;
            x[0] = 0;
            break;
        }
        case 2: {
            uint64_t const x0 = x[0], x1 = x[1];
            x[3] = (x1 << b) | up(x0);
            x[2] = x0 << b;
            x[1] = 0;
            x[0] = 0;
            break;
        }
        default: {
            uint64_t const x0 = x[0];
            x[3] = x0 << b;
            x[2] = 0;
            x[1] = 0;
            x[0] = 0;
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
        // gcc knows the gas was not negative before this charge, and turns
        // the test into a compare with -1, a constant it must load first:
        // hidden from it, the test is one bltz.
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
        if (MONAD_UNLIKELY(!MONAD_VM_ANALYSIS.is_jumpdest16(dst))) {
            ctx.exit(Error);
        }
        auto const *ip = MONAD_VM_ANALYSIS.code() + dst;
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
            static_cast<uint64_t>(
                stack_top - (stack_bottom - MONAD_VM_STACK_BOTTOM_BIAS)),
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
    add(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ADD);
#if defined(MONAD_ZKVM_ZISK)
        // Name a, then step to the sum's slot, which is the new top: the old
        // top dies at that store, so add256's output register cannot take a3
        // from under the new one and cost a move.
        ctx.add256_params.a = reinterpret_cast<uint64_t const *>(stack_top);
        --stack_top;
        MONAD_VM_LAUNDER(stack_top);
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
    mul(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MUL, runtime::mul);

        MONAD_VM_NEXT(MUL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SUB);
#if defined(MONAD_ZKVM_ZISK)
        // Name a, then step to the new top, as ADD does. The barrier keeps the
        // store ahead of b's loads, which gcc would otherwise schedule first.
        ctx.sub256_params.a = reinterpret_cast<uint64_t const *>(stack_top);
        asm volatile("" ::: "memory");
        --stack_top;
        MONAD_VM_LAUNDER(stack_top);
        // a - b = a + ~b + 1: complement b where it lies, then let add256 add
        // it to a with a carry-in of 1, back into the same slot.
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(DIV, runtime::udiv);

        MONAD_VM_NEXT(DIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SDIV, runtime::sdiv);

        MONAD_VM_NEXT(SDIV);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MOD, runtime::umod);

        MONAD_VM_NEXT(MOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SMOD, runtime::smod);

        MONAD_VM_NEXT(SMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(ADDMOD, runtime::addmod);

        MONAD_VM_NEXT(ADDMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(MULMOD, runtime::mulmod);

        MONAD_VM_NEXT(MULMOD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(EXP, runtime::exp<base_traits<traits>>);

        MONAD_VM_NEXT(EXP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SIGNEXTEND);
        auto &&[b, x] = top_two(stack_top);
#if defined(MONAD_ZKVM_ZISK)
        // Solidity's int8 to int64: the sign byte in the low word, which two
        // shifts extend, and its sign in the three words above -- against
        // the general case's masks and run of stores at a run-time index.
        if ((b[1] | b[2] | b[3]) == 0 && b[0] < 8) {
            unsigned const shift = static_cast<unsigned>(56 - 8 * b[0]);
            int64_t const low = static_cast<int64_t>(x[0] << shift) >> shift;
            uint64_t const sign = static_cast<uint64_t>(low >> 63);
            x[0] = static_cast<uint64_t>(low);
            x[1] = sign;
            x[2] = sign;
            x[3] = sign;
            MONAD_VM_NEXT(SIGNEXTEND);
        }
#endif
        signextend_to(b, x);

        MONAD_VM_NEXT(SIGNEXTEND);
    }

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(LT);
#if defined(MONAD_ZKVM_ZISK)
        // The result's slot is the new top: step there first, so the old top
        // dies here instead of beside the new one.
        --stack_top;
        MONAD_VM_LAUNDER(stack_top);
        if constexpr (has_slots<traits>) {
            // The result goes in a7 to a head of the follower's slot
            // (bool_offset, execute.cpp), which writes it, or branches on it
            // for PUSH2 JUMPI without writing it.
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(*(stack_top + 1) < *stack_top));
        }
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
    gt(runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(GT);
#if defined(MONAD_ZKVM_ZISK)
        // As LT.
        --stack_top;
        MONAD_VM_LAUNDER(stack_top);
        if constexpr (has_slots<traits>) {
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(*(stack_top + 1) > *stack_top));
        }
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
    slt(runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SLT);
#if defined(MONAD_ZKVM_ZISK)
        // As LT.
        --stack_top;
        MONAD_VM_LAUNDER(stack_top);
        if constexpr (has_slots<traits>) {
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(slt(*(stack_top + 1), *stack_top)));
        }
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
    sgt(runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(SGT);
#if defined(MONAD_ZKVM_ZISK)
        // As LT.
        --stack_top;
        MONAD_VM_LAUNDER(stack_top);
        if constexpr (has_slots<traits>) {
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(slt(*stack_top, *(stack_top + 1))));
        }
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
    eq(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse EQ PUSH2 <dst16> JUMPI. EQ frees a stack slot, so PUSH2
        // cannot overflow once EQ's operands are validated.
        uint8_t const monad_vm_op2 = *(instr_ptr + 1);
        if (monad_vm_op2 == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            static constexpr auto monad_vm_req =
                fused_requirements<traits, EQ, PUSH2, JUMPI>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                gas_remaining += monad_vm_req.gas;
                MONAD_VM_CHECK(EQ);
                // EQ frees a slot, so PUSH2 cannot overflow a valid stack.
                MONAD_DEBUG_ASSERT(
                    (stack_top - 1) -
                        (stack_bottom - MONAD_VM_STACK_BOTTOM_BIAS) <
                    static_cast<std::ptrdiff_t>(
                        runtime::EvmStackAllocatorMeta::size));
                MONAD_VM_CHARGE(PUSH2);
                // PUSH2 adds one value, restoring the original stack height.
                MONAD_VM_CHECK_AT(JUMPI, 0);
            }
            // Keep EQ's result in a C++ bool instead of the EVM stack, the
            // words compared by DMA (zisk_equal32): one step where gcc's
            // compare is three a word, and half of EQ's run all four.
            bool const monad_vm_taken = zisk_equal32(
                reinterpret_cast<uint64_t const *>(stack_top),
                reinterpret_cast<uint64_t const *>(stack_top - 1));
            instr_ptr =
                fused_branch(ctx, instr_ptr, monad_vm_taken, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top - 2,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(EQ);
#if defined(MONAD_ZKVM_ZISK)
        if constexpr (has_slots<traits>) {
            // As LT's, the result to the follower's head; the words compared
            // by DMA, as for the fused JUMPI above.
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                monad_vm_op2,
                stack_top - 1,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(zisk_equal32(
                    reinterpret_cast<uint64_t const *>(stack_top),
                    reinterpret_cast<uint64_t const *>(stack_top - 1))));
        }
#endif
        auto &&[a, b] = top_two(stack_top);
        b = (a == b);

#if defined(MONAD_ZKVM_ZISK)
        MONAD_VM_NEXT_OP(EQ, monad_vm_op2);
#else
        MONAD_VM_NEXT(EQ);
#endif
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse ISZERO PUSH2 <dst16> JUMPI without storing the test result.
        uint8_t const monad_vm_op2 = *(instr_ptr + 1);
        if (monad_vm_op2 == static_cast<std::uint8_t>(PUSH2) &&
            *(instr_ptr + 4) == static_cast<std::uint8_t>(JUMPI)) {
            static constexpr auto monad_vm_req =
                fused_requirements<traits, ISZERO, PUSH2, JUMPI>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                gas_remaining += monad_vm_req.gas;
                MONAD_VM_CHECK(ISZERO);
                MONAD_VM_CHECK_AT(PUSH2, 0);
                MONAD_VM_CHECK_AT(JUMPI, 1);
            }
            bool const monad_vm_taken = !*stack_top;
            instr_ptr =
                fused_branch(ctx, instr_ptr, monad_vm_taken, gas_remaining);
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top - 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(ISZERO);
#if defined(MONAD_ZKVM_ZISK)
        if constexpr (has_slots<traits>) {
            // As LT's, the result to the follower's head.
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                monad_vm_op2,
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(!*stack_top));
        }
#endif
        auto &a = *stack_top;
        a = !a;

#if defined(MONAD_ZKVM_ZISK)
        MONAD_VM_NEXT_OP(ISZERO, monad_vm_op2);
#else
        MONAD_VM_NEXT(ISZERO);
#endif
    }

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
    or_(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
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
    shl(runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
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
    shr(runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
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
    sar(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
    clz(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SHA3, runtime::sha3<base_traits<traits>>);

        MONAD_VM_NEXT(SHA3);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(ADDRESS);
        push(stack_top, runtime::uint256_from_address(ctx.env.recipient));

        MONAD_VM_NEXT(ADDRESS);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            BALANCE, runtime::balance<base_traits<traits>>);

        MONAD_VM_NEXT(BALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CALLER);
        push(stack_top, runtime::uint256_from_address(ctx.env.sender));

        MONAD_VM_NEXT(CALLER);
    }

#if defined(MONAD_ZKVM_ZISK)
    // Whether the call carries no value: the big-endian word in four reads.
    [[gnu::always_inline]] inline bool
    call_value_is_zero(runtime::Context const &ctx) noexcept
    {
        // Four loads, not one copy: a 32-byte memcpy is a DMA to the stack
        // and four reloads.
        unsigned char const *const v = ctx.env.value.bytes;
        uint64_t w0, w1, w2, w3;
        __builtin_memcpy(&w0, v, 8);
        __builtin_memcpy(&w1, v + 8, 8);
        __builtin_memcpy(&w2, v + 16, 8);
        __builtin_memcpy(&w3, v + 24, 8);
        return (w0 | w1 | w2 | w3) == 0;
    }

    // The via-IR ABI decoder's bound, at q:
    //
    //     PUSH0 (or PUSH1 <k>) CALLDATASIZE PUSH1 3 NOT ADD SLT
    //     PUSH2 <revert> JUMPI
    //
    // its length in bytes when the JUMPI is not taken -- the calldata past
    // the selector at least k long -- and 0 when the bytes differ or the
    // jump is taken. Pushes three words at most.
    [[gnu::always_inline]] inline size_t ir_bound_length(
        runtime::Context const &ctx, uint8_t const *const q) noexcept
    {
        bool const push0 = q[0] == static_cast<std::uint8_t>(PUSH0);
        if (!push0 && q[0] != static_cast<std::uint8_t>(PUSH1)) {
            return 0;
        }
        size_t const k = push0 ? 0 : q[1];
        auto const *const r = q + (push0 ? 1 : 2);
        if (!(r[0] == static_cast<std::uint8_t>(CALLDATASIZE) &&
              r[1] == static_cast<std::uint8_t>(PUSH1) && r[2] == 3 &&
              r[3] == static_cast<std::uint8_t>(NOT) &&
              r[4] == static_cast<std::uint8_t>(ADD) &&
              r[5] == static_cast<std::uint8_t>(SLT) &&
              r[6] == static_cast<std::uint8_t>(PUSH2) &&
              r[9] == static_cast<std::uint8_t>(JUMPI))) {
            return 0;
        }
        uint64_t const size = ctx.env.input_data_size;
        if (size < 4 || size - 4 < k) {
            return 0;
        }
        return static_cast<size_t>(r - q) + 10;
    }

    // The non-payable test of Solidity's legacy code generator,
    //
    //     CALLVALUE DUP1 ISZERO PUSH2 <ok> JUMPI PUSH1 0 DUP1 REVERT
    //     ok: JUMPDEST POP                     (or PUSH0 DUP1 REVERT ..)
    //
    // without value: the jump to ok taken, the stack as it was. callvalue
    // tail-calls it when DUP1 follows; other bytes, a value and too full a
    // stack run the CALLVALUE here, as callvalue does.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void callvalue_nonpayable(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const *const p = instr_ptr;
        auto const monad_vm_is = [p](size_t const k, auto const op) {
            return p[k] == static_cast<std::uint8_t>(op);
        };
        // PUSH1 0 or PUSH0 before the DUP1 REVERT: ok is one byte nearer with
        // PUSH0. Each arm reads its bytes at constant offsets.
        size_t monad_vm_ok;
        bool monad_vm_tail;
        if (monad_vm_is(7, PUSH0)) {
            monad_vm_ok = 10;
            monad_vm_tail = monad_vm_is(8, DUP1) && monad_vm_is(9, REVERT) &&
                            monad_vm_is(10, JUMPDEST) && monad_vm_is(11, POP);
        }
        else {
            monad_vm_ok = 11;
            monad_vm_tail = monad_vm_is(7, PUSH1) && p[8] == 0 &&
                            monad_vm_is(9, DUP1) && monad_vm_is(10, REVERT) &&
                            monad_vm_is(11, JUMPDEST) && monad_vm_is(12, POP);
        }
        size_t const monad_vm_dst = detail::load_be_k<2>(p + 4);
        size_t const monad_vm_pos =
            static_cast<size_t>(p - MONAD_VM_ANALYSIS.code());
        // ok is a JUMPDEST where these bytes put it: an instruction's first
        // byte, read from this CALLVALUE on, so no map is needed.
        if (MONAD_UNLIKELY(
                !(monad_vm_tail && monad_vm_is(2, ISZERO) &&
                  monad_vm_is(3, PUSH2) && monad_vm_is(6, JUMPI) &&
                  monad_vm_dst == monad_vm_pos + monad_vm_ok &&
                  stack_top + 3 <= MONAD_VM_STACK_LIMIT &&
                  call_value_is_zero(ctx)))) {
            // The CALLVALUE as callvalue runs it: dispatched to, it would
            // call this twin again.
            MONAD_VM_CHECK(CALLVALUE);
            push(stack_top, load_be<uint256_t>(ctx.env.value));
            MONAD_VM_NEXT(CALLVALUE);
        }
        // The taken JUMPI's checkpoint, on the JUMPDEST it lands on, after
        // the POP's charge: an exceptional halt either way.
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
        MONAD_VM_FUSED_NEXT(monad_vm_ok + 2, 0);
    }

    // The non-payable test of the via-IR code generator, CALLVALUE PUSH2
    // <revert> JUMPI, without value: the JUMPI not taken; and the decoder's
    // bound that commonly follows (ir_bound_length) with it when it holds.
    // callvalue tail-calls it when PUSH2 follows; other bytes, a value and
    // too full a stack run the CALLVALUE here, as callvalue does.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void callvalue_ir(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const *const p = instr_ptr;
        if (MONAD_UNLIKELY(
                !(p[4] == static_cast<std::uint8_t>(JUMPI) &&
                  stack_top + 3 <= MONAD_VM_STACK_LIMIT &&
                  call_value_is_zero(ctx)))) {
            // The CALLVALUE as callvalue runs it: dispatched to, it would
            // call this twin again.
            MONAD_VM_CHECK(CALLVALUE);
            push(stack_top, load_be<uint256_t>(ctx.env.value));
            MONAD_VM_NEXT(CALLVALUE);
        }
        // Pure opcodes and JUMPIs not taken: the sign of the count is left
        // to the next checkpoint (MONAD_VM_FUSED_CHARGE_PURE).
        gas_remaining -= static_gas<traits, CALLVALUE, PUSH2, JUMPI>();
        size_t const monad_vm_bound = ir_bound_length(ctx, p + 5);
        if (monad_vm_bound != 0) {
            gas_remaining -= p[5] == static_cast<std::uint8_t>(PUSH0)
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
        instr_ptr += 5 + monad_vm_bound;
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }
#endif

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Solidity reads the call's value for its non-payable test, each
        // generator's in a twin: DUP1 follows in the legacy one, PUSH2 in
        // the via-IR one.
        if (instr_ptr[1] == static_cast<std::uint8_t>(DUP1)) {
            MONAD_VM_MUST_TAIL return callvalue_nonpayable<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        if (instr_ptr[1] == static_cast<std::uint8_t>(PUSH2)) {
            MONAD_VM_MUST_TAIL return callvalue_ir<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(CALLVALUE);
        push(stack_top, load_be<uint256_t>(ctx.env.value));

        MONAD_VM_NEXT(CALLVALUE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(CALLDATALOAD);
        // Called directly: it reads the environment and never gas, so
        // call_runtime's sync would be a store and a reload for nothing.
        runtime::calldataload(&ctx, stack_top, stack_top);

        MONAD_VM_NEXT(CALLDATALOAD);
    }

#if defined(MONAD_ZKVM_ZISK)
    // The selector's extraction at q, in one of three forms,
    //
    //     PUSH1 0 CALLDATALOAD PUSH1 0xe0 SHR
    //     PUSH0 CALLDATALOAD PUSH1 0xe0 SHR
    //     PUSH1 0 CALLDATALOAD PUSH29 1 << 224 SWAP1 DIV PUSH4 0xffffffff AND
    //
    // the last the code generators before 0.5 wrote: its length in bytes, its
    // gas charged and the selector pushed at stack_top + 1; 0 for other bytes,
    // with nothing done. Each form reads its bytes at constant offsets. The
    // forms push one word at most above stack_top + 1.
    template <Traits traits>
    [[gnu::always_inline]] inline size_t push_selector(
        runtime::Context const &ctx, uint8_t const *const q,
        uint256_t *const stack_top, int64_t &gas_remaining)
    {
        auto const is = [q](size_t const k, auto const op) {
            return q[k] == static_cast<std::uint8_t>(op);
        };
        size_t length = 0;
        if (is(0, PUSH0)) {
            if (is(1, CALLDATALOAD) && is(2, PUSH1) && q[3] == 0xe0 &&
                is(4, SHR)) {
                gas_remaining -=
                    static_gas<traits, PUSH0, CALLDATALOAD, PUSH1, SHR>();
                length = 5;
            }
        }
        else if (is(0, PUSH1) && q[1] == 0 && is(2, CALLDATALOAD)) {
            if (is(3, PUSH1) && q[4] == 0xe0 && is(5, SHR)) {
                gas_remaining -=
                    static_gas<traits, PUSH1, CALLDATALOAD, PUSH1, SHR>();
                length = 6;
            }
            else if (
                is(3, PUSH29) && q[4] == 1 && is(33, SWAP1) && is(34, DIV) &&
                is(35, PUSH4) && is(40, AND)) {
                uint64_t w0, w1, w2;
                uint32_t w3, mask;
                __builtin_memcpy(&w0, q + 5, 8);
                __builtin_memcpy(&w1, q + 13, 8);
                __builtin_memcpy(&w2, q + 21, 8);
                __builtin_memcpy(&w3, q + 29, 4);
                __builtin_memcpy(&mask, q + 36, 4);
                if ((w0 | w1 | w2 | w3) == 0 && mask == 0xffffffffu) {
                    gas_remaining -= static_gas<
                        traits,
                        PUSH1,
                        CALLDATALOAD,
                        PUSH29,
                        SWAP1,
                        DIV,
                        PUSH4,
                        AND>();
                    length = 41;
                }
            }
        }
        if (length != 0) {
            stack_top[1] = uint256_t{detail::load_be_k<4>(ctx.env.input_data)};
        }
        return length;
    }

    // Solidity's dispatch prologue, from the CALLDATASIZE, over [.. 4] and at
    // least four bytes of calldata, in either of its forms,
    //
    //     PUSH1 4 CALLDATASIZE LT PUSH2 <fallback> JUMPI          (not taken)
    //     PUSH1 4 CALLDATASIZE LT ISZERO PUSH2 <dispatch> JUMPI   (taken)
    //
    // the 4 consumed and the selector's extraction that follows, at the
    // straight line or the dispatch, run with it (push_selector): the selector
    // in place of the 4. calldatasize tail-calls it when LT follows; other
    // bytes, a shorter calldata and too full a stack run the CALLDATASIZE
    // here, as calldatasize does. An invalid destination exits as the JUMPI
    // would.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void calldata_selector(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const *const p = instr_ptr;
        auto const monad_vm_is = [p](size_t const k, auto const op) {
            return p[k] == static_cast<std::uint8_t>(op);
        };
        uint256_t const &monad_vm_b = stack_top[0];
        bool const monad_vm_straight =
            monad_vm_is(2, PUSH2) && monad_vm_is(5, JUMPI);
        bool const monad_vm_taken = monad_vm_is(2, ISZERO) &&
                                    monad_vm_is(3, PUSH2) &&
                                    monad_vm_is(6, JUMPI);
        if (MONAD_UNLIKELY(
                !((monad_vm_straight || monad_vm_taken) &&
                  ctx.env.input_data_size >= 4 && stack_top >= stack_bottom &&
                  stack_top + 1 <= MONAD_VM_STACK_LIMIT && monad_vm_b[0] == 4 &&
                  (monad_vm_b[1] | monad_vm_b[2] | monad_vm_b[3]) == 0))) {
            // The CALLDATASIZE as calldatasize runs it: dispatched to, it
            // would call this twin again.
            MONAD_VM_CHECK(CALLDATASIZE);
            push(stack_top, ctx.env.input_data_size);
            MONAD_VM_NEXT(CALLDATASIZE);
        }
        // Pure opcodes and a JUMPI: the sign of the count is left to the next
        // checkpoint, which for the taken jump is its JUMPDEST (fused_branch).
        uint8_t const *monad_vm_q;
        if (monad_vm_straight) {
            gas_remaining -=
                static_gas<traits, CALLDATASIZE, LT, PUSH2, JUMPI>();
            monad_vm_q = p + 6;
        }
        else {
            gas_remaining -=
                static_gas<traits, CALLDATASIZE, LT, ISZERO, PUSH2, JUMPI>();
            monad_vm_q = fused_branch(ctx, p + 2, true, gas_remaining);
        }
        size_t const monad_vm_n = push_selector<traits>(
            ctx, monad_vm_q, stack_top - 1, gas_remaining);
        instr_ptr = monad_vm_q + monad_vm_n;
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top - (monad_vm_n == 0 ? 1 : 0),
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // The ABI decoder's bound on the calldata,
    //
    //     PUSH1 4 DUP1 CALLDATASIZE SUB PUSH1 <k> DUP2 LT ISZERO
    //     PUSH2 <decode> JUMPI
    //
    // from the CALLDATASIZE, over [.. 4 b]: b replaced by the length past it,
    // and the jump taken when that length is at least k. calldatasize
    // tail-calls it when SUB follows; other bytes, a calldata shorter than b
    // (the length wraps) and too full a stack run the CALLDATASIZE here, as
    // calldatasize does. An invalid destination exits as the JUMPI would.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void calldata_bound(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const *const p = instr_ptr;
        auto const monad_vm_is = [p](size_t const k, auto const op) {
            return p[k] == static_cast<std::uint8_t>(op);
        };
        uint256_t &monad_vm_b = stack_top[0];
        uint64_t const monad_vm_size = ctx.env.input_data_size;
        if (MONAD_UNLIKELY(
                !(monad_vm_is(2, PUSH1) && monad_vm_is(4, DUP2) &&
                  monad_vm_is(5, LT) && monad_vm_is(6, ISZERO) &&
                  monad_vm_is(7, PUSH2) && monad_vm_is(10, JUMPI) &&
                  stack_top >= stack_bottom &&
                  stack_top + 2 <= MONAD_VM_STACK_LIMIT &&
                  (monad_vm_b[1] | monad_vm_b[2] | monad_vm_b[3]) == 0 &&
                  monad_vm_b[0] <= monad_vm_size))) {
            // The CALLDATASIZE as calldatasize runs it: dispatched to, it
            // would call this twin again.
            MONAD_VM_CHECK(CALLDATASIZE);
            push(stack_top, ctx.env.input_data_size);
            MONAD_VM_NEXT(CALLDATASIZE);
        }
        // Pure opcodes and a JUMPI: fused_branch tests the sign of the count
        // at the JUMPDEST a taken jump lands on (MONAD_VM_FUSED_CHARGE_PURE).
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
        uint64_t const monad_vm_len = monad_vm_size - monad_vm_b[0];
        monad_vm_b = uint256_t{monad_vm_len};
        instr_ptr =
            fused_branch(ctx, p + 6, monad_vm_len >= p[3], gas_remaining);
        MONAD_VM_LAUNDER(instr_ptr);
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }
#endif

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Solidity reads the calldata's size for two idioms, each with a
        // twin: the dispatch prologue (LT follows) and the ABI decoder's
        // bound (SUB follows).
        if (instr_ptr[1] == static_cast<std::uint8_t>(LT)) {
            MONAD_VM_MUST_TAIL return calldata_selector<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        if (instr_ptr[1] == static_cast<std::uint8_t>(SUB)) {
            MONAD_VM_MUST_TAIL return calldata_bound<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
#endif
        MONAD_VM_CHECK(CALLDATASIZE);
        push(stack_top, ctx.env.input_data_size);

        MONAD_VM_NEXT(CALLDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CALLDATACOPY, runtime::calldatacopy<base_traits<traits>>);

        MONAD_VM_NEXT(CALLDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CODESIZE);
        push(stack_top, ctx.env.code_size);

        MONAD_VM_NEXT(CODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CODECOPY, runtime::codecopy<base_traits<traits>>);

        MONAD_VM_NEXT(CODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GASPRICE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->tx_gas_price));

        MONAD_VM_NEXT(GASPRICE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODESIZE, runtime::extcodesize<base_traits<traits>>);

        MONAD_VM_NEXT(EXTCODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODECOPY, runtime::extcodecopy<base_traits<traits>>);

        MONAD_VM_NEXT(EXTCODECOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(RETURNDATASIZE);
        push(stack_top, ctx.env.return_data_size);

        MONAD_VM_NEXT(RETURNDATASIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            RETURNDATACOPY, runtime::returndatacopy<base_traits<traits>>);

        MONAD_VM_NEXT(RETURNDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODEHASH, runtime::extcodehash<base_traits<traits>>);

        MONAD_VM_NEXT(EXTCODEHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BLOCKHASH, runtime::blockhash);

        MONAD_VM_NEXT(BLOCKHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(TIMESTAMP);
        push(stack_top, ctx.env.tx_context->block_timestamp);

        MONAD_VM_NEXT(TIMESTAMP);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(NUMBER);
        push(stack_top, ctx.env.tx_context->block_number);

        MONAD_VM_NEXT(NUMBER);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GASLIMIT);
        push(stack_top, ctx.env.tx_context->block_gas_limit);

        MONAD_VM_NEXT(GASLIMIT);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(CHAINID);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->chain_id));

        MONAD_VM_NEXT(CHAINID);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(SELFBALANCE, runtime::selfbalance);

        MONAD_VM_NEXT(SELFBALANCE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(BASEFEE);
        push(stack_top, load_be<uint256_t>(ctx.env.tx_context->block_base_fee));

        MONAD_VM_NEXT(BASEFEE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(BLOBHASH, runtime::blobhash);

        MONAD_VM_NEXT(BLOBHASH);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
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
    template <Traits traits>
    [[gnu::noinline, gnu::cold]] MONAD_VM_TWIN_CALL void mload_grow(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        call_runtime(
            runtime::mload<base_traits<traits>>, ctx, stack_top, gas_remaining);

        MONAD_VM_NEXT(MLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK_OWN_GAS(MLOAD);

        // No gas sync: only the growth path charges, and mload_grow syncs
        // through call_runtime. An out-of-range offset exits OutOfGas, whose
        // result carries no gas.
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mload_grow<quiet_traits<traits>>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        runtime::mload_at<base_traits<traits>>(&ctx, stack_top, offset);

        MONAD_VM_NEXT(MLOAD);
    }

    // What mstore_grow does not take, through the generic path: capacity
    // growth, and a size past the transaction's memory limit.
    template <Traits traits>
    [[gnu::noinline, gnu::cold]] MONAD_VM_TWIN_CALL void mstore_slow(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        call_runtime(
            runtime::mstore<base_traits<traits>>,
            ctx,
            stack_top,
            gas_remaining);

        MONAD_VM_NEXT(MSTORE);
    }

    // Growth within the capacity, which MSTORE takes on 40 % of executions:
    // it writes where nothing has been written yet. The cost is charged on
    // the register gas, and the only calls are tail calls, so neither this
    // twin nor mstore needs a frame.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void mstore_grow(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
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
            MONAD_VM_MUST_TAIL return mstore_slow<quiet_traits<traits>>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        auto const new_cost =
            runtime::Context::memory_cost_from_word_count<traits>(word_count);
        gas_remaining -= new_cost - ctx.memory.cost;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        ctx.memory.size = *new_size;
        ctx.memory.cost = new_cost;
        runtime::mstore_at<base_traits<traits>>(&ctx, offset, stack_top - 1);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        // Held in a3 and a5 through empty asms, so gcc does not take them
        // for temporaries and copy the pointers away at the first instruction.
        MONAD_VM_LAUNDER(stack_top);
        MONAD_VM_LAUNDER_AS_CALLED(instr_ptr);
        MONAD_VM_CHECK_OWN_GAS(MSTORE);

        // A store inside the memory charges nothing, so no gas sync, and it
        // makes no call, so no frame.
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        runtime::mstore_at<base_traits<traits>>(&ctx, offset, stack_top - 1);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            MSTORE8, runtime::mstore8<base_traits<traits>>);

        MONAD_VM_NEXT(MSTORE8);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            MCOPY, runtime::mcopy<base_traits<traits>>);

        MONAD_VM_NEXT(MCOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SSTORE, runtime::sstore<base_traits<traits>>);

        MONAD_VM_NEXT(SSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SLOAD, runtime::sload<base_traits<traits>>);

        MONAD_VM_NEXT(SLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(TSTORE, runtime::tstore);

        MONAD_VM_NEXT(TSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(TLOAD, runtime::tload);

        MONAD_VM_NEXT(TLOAD);
    }

    // Execution Intercode
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
       uint256_t const *stack_bottom, uint256_t *stack_top,
       int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(PC);
        push(stack_top, instr_ptr - MONAD_VM_ANALYSIS.code());

        MONAD_VM_NEXT(PC);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(MSIZE);
        push(stack_top, ctx.memory.size);

        MONAD_VM_NEXT(MSIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(GAS);
        push(stack_top, gas_remaining);

        MONAD_VM_NEXT(GAS);
    }

    // Stack

    // PUSH1's fused SHR and SAR, apart from push<1>. A 256-bit shift by a
    // runtime amount wants more registers than the caller-saved ones left
    // beside the handler's arguments, and the callee-saved one it takes inside
    // push<1> puts a frame on every fused PUSH1, ADD and SHL included. Gas and
    // stack are checked, and instr_ptr is still on the PUSH1.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_shr(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        *stack_top >>= uint256_t{*(instr_ptr + 1)};
        MONAD_VM_FUSED_NEXT(3, 0);
    }

    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_sar(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        *stack_top = sar(uint256_t{*(instr_ptr + 1)}, *stack_top);
        MONAD_VM_FUSED_NEXT(3, 0);
    }

#if defined(MONAD_ZKVM_ZISK)
    // The rest of PUSH1 1 PUSH1 1 PUSH1 <k> SHL SUB, the mask 2^k - 1 that
    // Solidity builds to clean an address (k = 160) or a uint<k>, and of the
    // AND that applies it more often than not. push1_then's PUSH1 PUSH1 arm
    // dispatches here, instr_ptr on the third PUSH1 and stack_top on the
    // second one's slot; the first one's slot takes the mask, or the AND
    // consumes them. Neither one is read, so the arm need not write them.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_mask(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const monad_vm_k = static_cast<size_t>(*(instr_ptr + 1));
        // The word holding bit k, whose low k % 64 bits the mask sets, the
        // words below it all ones and those above it zero.
        size_t const monad_vm_w = monad_vm_k >> 6;
        uint64_t const monad_vm_low = (uint64_t{1} << (monad_vm_k & 63)) - 1;
        if (*(instr_ptr + 4) == static_cast<std::uint8_t>(AND)) {
            // After the ones: the value under them.
            static constexpr auto monad_vm_req =
                fused_requirements<traits, PUSH1, SHL, SUB, AND>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                gas_remaining += monad_vm_req.gas;
                MONAD_VM_CHECK(PUSH1);
                MONAD_VM_CHECK_AT(SHL, 1);
                MONAD_VM_CHECK_AT(SUB, 0);
                MONAD_VM_CHECK_AT(AND, -1);
            }
            auto &monad_vm_x = *(stack_top - 2);
            if (monad_vm_w == 2) {
                monad_vm_x[2] &= monad_vm_low;
                monad_vm_x[3] = 0;
            }
            else if (monad_vm_w == 1) {
                monad_vm_x[1] &= monad_vm_low;
                monad_vm_x[2] = 0;
                monad_vm_x[3] = 0;
            }
            else if (monad_vm_w == 3) {
                monad_vm_x[3] &= monad_vm_low;
            }
            else {
                monad_vm_x[0] &= monad_vm_low;
                monad_vm_x[1] = 0;
                monad_vm_x[2] = 0;
                monad_vm_x[3] = 0;
            }
            MONAD_VM_FUSED_NEXT(5, -2);
        }
        static constexpr auto monad_vm_req =
            fused_requirements<traits, PUSH1, SHL, SUB>();
        if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(PUSH1);
            MONAD_VM_CHECK_AT(SHL, 1);
            MONAD_VM_CHECK_AT(SUB, 0);
        }
        auto &monad_vm_y = *(stack_top - 1);
        uint64_t const monad_vm_ones = ~uint64_t{0};
        if (monad_vm_w == 2) {
            monad_vm_y[0] = monad_vm_ones;
            monad_vm_y[1] = monad_vm_ones;
            monad_vm_y[2] = monad_vm_low;
            monad_vm_y[3] = 0;
        }
        else if (monad_vm_w == 1) {
            monad_vm_y[0] = monad_vm_ones;
            monad_vm_y[1] = monad_vm_low;
            monad_vm_y[2] = 0;
            monad_vm_y[3] = 0;
        }
        else if (monad_vm_w == 3) {
            monad_vm_y[0] = monad_vm_ones;
            monad_vm_y[1] = monad_vm_ones;
            monad_vm_y[2] = monad_vm_ones;
            monad_vm_y[3] = monad_vm_low;
        }
        else {
            monad_vm_y[0] = monad_vm_low;
            monad_vm_y[1] = 0;
            monad_vm_y[2] = 0;
            monad_vm_y[3] = 0;
        }
        MONAD_VM_FUSED_NEXT(4, -1);
    }

    // PUSH1 and the opcode after its immediate, OP, run as one, instr_ptr on
    // the PUSH1. On a revision with slots, PUSH1 dispatches to the head of
    // OP's slot (push<1>), which for these followers jumps here (execute.cpp),
    // PUSH1's own stack test made, and passes OP's handler as HANDLER; push<1>
    // tests the follower and calls this on the others.
    template <uint8_t OP, Traits traits, InstrEval HANDLER = nullptr>
    MONAD_VM_INSTRUCTION_CALL void push1_then(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        if constexpr (OP == PUSH1 && has_slots<traits>) {
            // PUSH1 1 PUSH1 1 PUSH1 <k> SHL SUB builds the mask 2^k - 1,
            // which push1_mask finishes from the two ones pushed. Any other
            // PUSH1 <a> PUSH1 <b> pushes a, and the second PUSH1 lands in its
            // own follower's slot, as push<1> would make it.
            uint8_t const monad_vm_imm1 = *(instr_ptr + 1);
            if (MONAD_UNLIKELY(
                    monad_vm_imm1 == 1 && *(instr_ptr + 3) == 1 &&
                    *(instr_ptr + 4) == static_cast<std::uint8_t>(PUSH1) &&
                    *(instr_ptr + 6) == static_cast<std::uint8_t>(SHL) &&
                    *(instr_ptr + 7) == static_cast<std::uint8_t>(SUB))) {
                static constexpr auto monad_vm_reqp =
                    fused_requirements<traits, PUSH1, PUSH1>();
                if (MONAD_UNLIKELY(
                        !MONAD_VM_FUSED_CHARGE_PURE(monad_vm_reqp))) {
                    gas_remaining += monad_vm_reqp.gas;
                    MONAD_VM_CHECK(PUSH1);
                    MONAD_VM_CHECK_AT(PUSH1, 1);
                }
                // The ones are not written: push1_mask writes the mask over
                // the first, or ANDs the word under them, and reads neither.
                instr_ptr += 4;
                MONAD_VM_MUST_TAIL return push1_mask<traits>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top + 2,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            interpreter::push(stack_top, uint256_t{monad_vm_imm1});
            if (MONAD_UNLIKELY(stack_top + 1 >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            // The second PUSH1 two bytes further behind, modulo the copies.
            constexpr unsigned monad_vm_lag2 = (lag_of<traits> + 2) % lag_count;
            MONAD_VM_LEAD_DISPATCH(
                lead_offset(monad_vm_lag2, 1),
                *(instr_ptr + 4),
                stack_top + 1,
                (gas_remaining - static_gas<traits, PUSH1>()),
                instr_ptr + 2 - monad_vm_lag2);
        }
        else if constexpr (OP == PUSH1) {
            // Fuse PUSH1 <a> PUSH1 <b>, saving one dispatch.
            // The pair needs two free slots and 6 gas; the fallback preserves
            // per-opcode checks and error order.
            // Zero padding supplies a missing second immediate.
            static constexpr auto monad_vm_reqp =
                fused_requirements<traits, PUSH1, PUSH1>();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_reqp))) {
                gas_remaining += monad_vm_reqp.gas;
                MONAD_VM_CHECK(PUSH1);
                MONAD_VM_CHECK_AT(PUSH1, 1);
            }
            // Both immediates read before either store, so the old
            // instr_ptr dies before the dispatch forms the new one.
            uint8_t const monad_vm_imm1 = *(instr_ptr + 1);
            uint8_t const monad_vm_imm2 = *(instr_ptr + 3);
            interpreter::push(stack_top, uint256_t{monad_vm_imm1});
            interpreter::push(stack_top + 1, uint256_t{monad_vm_imm2});
            // Two ones before PUSH1 <k> SHL SUB build a mask, which
            // push1_mask finishes: the dispatch's target, not a call of
            // its own, which would copy the arguments away on every PUSH1.
            instr_ptr += 4;
            MONAD_VM_LAUNDER(instr_ptr);
            bool const monad_vm_mask =
                monad_vm_imm1 == 1 && monad_vm_imm2 == 1 &&
                *instr_ptr == static_cast<std::uint8_t>(PUSH1) &&
                *(instr_ptr + 2) == static_cast<std::uint8_t>(SHL) &&
                *(instr_ptr + 3) == static_cast<std::uint8_t>(SUB);
            // The dispatch's target takes instr_ptr where it is, as a
            // handler that does not lag.
            auto const monad_vm_next = monad_vm_mask
                                           ? &push1_mask<base_traits<traits>>
                                           : MONAD_VM_TABLE_REF[*instr_ptr];
            MONAD_VM_MUST_TAIL return monad_vm_next(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top + 2,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == MLOAD || OP == MSTORE) {
            // The offset is the immediate: no word to read and bound, and
            // inside the memory MLOAD and MSTORE charge only their static
            // gas, which neither tests (stack.hpp). Outside, the push and
            // then the follower's handler, which grows the memory.
            auto const monad_vm_k = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(*(instr_ptr + 1)));
            if constexpr (OP == MLOAD) {
                if (MONAD_LIKELY(ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH1, MLOAD>();
                    runtime::mload_at<base_traits<traits>>(
                        &ctx, stack_top + 1, monad_vm_k);
                    MONAD_VM_FUSED_NEXT(3, 1);
                }
            }
            else {
                // MSTORE's value is the top.
                if (MONAD_LIKELY(
                        stack_top >= stack_bottom &&
                        ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH1, MSTORE>();
                    runtime::mstore_at<base_traits<traits>>(
                        &ctx, monad_vm_k, stack_top);
                    MONAD_VM_FUSED_NEXT(3, -1);
                }
            }
            interpreter::push(stack_top, uint256_t{*(instr_ptr + 1)});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP >= SWAP1 && OP <= SWAP4) {
            // The word n below the top moves up to where the push would put
            // the immediate, and the immediate takes its place.
            constexpr size_t monad_vm_n = OP - SWAP1 + 1;
            uint8_t const monad_vm_k = *(instr_ptr + 1);
            if (MONAD_LIKELY(stack_top + 1 - monad_vm_n >= stack_bottom)) {
                gas_remaining -= static_gas<
                    traits,
                    PUSH1,
                    static_cast<compiler::EvmOpCode>(OP)>();
                *(stack_top + 1) = *(stack_top + 1 - monad_vm_n);
                *(stack_top + 1 - monad_vm_n) = uint256_t{monad_vm_k};
                MONAD_VM_FUSED_NEXT(3, 1);
            }
            interpreter::push(stack_top, uint256_t{monad_vm_k});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == NOT) {
            // The immediate's complement, pushed.
            gas_remaining -= static_gas<traits, PUSH1, NOT>();
            interpreter::push(stack_top, ~uint256_t{*(instr_ptr + 1)});
            MONAD_VM_FUSED_NEXT(3, 1);
        }
        else if constexpr (OP == CALLDATALOAD) {
            // The calldata's word at the immediate, pushed: read in four
            // words where the calldata holds all of it.
            gas_remaining -= static_gas<traits, PUSH1, CALLDATALOAD>();
            uint8_t const monad_vm_k = *(instr_ptr + 1);
            auto const monad_vm_n =
                static_cast<int64_t>(ctx.env.input_data_size) -
                int64_t{monad_vm_k};
            auto &monad_vm_r = *(stack_top + 1);
            if (MONAD_LIKELY(monad_vm_n >= 32)) {
                auto const *const monad_vm_s = ctx.env.input_data + monad_vm_k;
                monad_vm_r[3] = load_be_unsafe<uint64_t>(monad_vm_s);
                monad_vm_r[2] = load_be_unsafe<uint64_t>(monad_vm_s + 8);
                monad_vm_r[1] = load_be_unsafe<uint64_t>(monad_vm_s + 16);
                monad_vm_r[0] = load_be_unsafe<uint64_t>(monad_vm_s + 24);
            }
            else if (monad_vm_n > 0) {
                monad_vm_r = runtime::uint256_load_bounded_be(
                    ctx.env.input_data + monad_vm_k, monad_vm_n);
            }
            else {
                monad_vm_r = 0;
            }
            MONAD_VM_FUSED_NEXT(3, 1);
        }
        else if constexpr (OP == AND) {
            // On the top, below the immediate: its low byte kept.
            uint8_t const monad_vm_k = *(instr_ptr + 1);
            if (MONAD_LIKELY(stack_top >= stack_bottom)) {
                gas_remaining -= static_gas<traits, PUSH1, AND>();
                auto &monad_vm_x = *stack_top;
                monad_vm_x[0] &= monad_vm_k;
                monad_vm_x[1] = 0;
                monad_vm_x[2] = 0;
                monad_vm_x[3] = 0;
                MONAD_VM_FUSED_NEXT(3, 0);
            }
            interpreter::push(stack_top, uint256_t{monad_vm_k});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == SIGNEXTEND) {
            // On the top, below the immediate: the byte it names extended
            // in two shifts in its word, the words above taking its sign;
            // a byte of the low word, int8 to int64 and Solidity's int24
            // ticks above all, without the word's index. A byte index of 31
            // or more and an empty stack take the push and then SIGNEXTEND's
            // handler, which HANDLER reaches by name: through the table, the
            // address formed in a6 makes gcc copy the arguments away at the
            // first instruction.
            uint8_t const monad_vm_k = *(instr_ptr + 1);
            if (MONAD_LIKELY(stack_top >= stack_bottom && monad_vm_k < 31)) {
                gas_remaining -= static_gas<traits, PUSH1, SIGNEXTEND>();
                auto &monad_vm_x = *stack_top;
                if (MONAD_LIKELY(monad_vm_k < 8)) {
                    unsigned const monad_vm_shift = 56u - 8u * monad_vm_k;
                    int64_t const monad_vm_low =
                        static_cast<int64_t>(monad_vm_x[0] << monad_vm_shift) >>
                        monad_vm_shift;
                    uint64_t const monad_vm_sign =
                        static_cast<uint64_t>(monad_vm_low >> 63);
                    monad_vm_x[0] = static_cast<uint64_t>(monad_vm_low);
                    monad_vm_x[1] = monad_vm_sign;
                    monad_vm_x[2] = monad_vm_sign;
                    monad_vm_x[3] = monad_vm_sign;
                }
                else {
                    unsigned const monad_vm_w = monad_vm_k >> 3;
                    unsigned const monad_vm_shift =
                        56u - 8u * (monad_vm_k & 7u);
                    int64_t const monad_vm_low =
                        static_cast<int64_t>(
                            monad_vm_x[monad_vm_w] << monad_vm_shift) >>
                        monad_vm_shift;
                    uint64_t const monad_vm_sign =
                        static_cast<uint64_t>(monad_vm_low >> 63);
                    monad_vm_x[monad_vm_w] =
                        static_cast<uint64_t>(monad_vm_low);
                    if (monad_vm_w == 1) {
                        monad_vm_x[2] = monad_vm_sign;
                        monad_vm_x[3] = monad_vm_sign;
                    }
                    else if (monad_vm_w == 2) {
                        monad_vm_x[3] = monad_vm_sign;
                    }
                }
                MONAD_VM_FUSED_NEXT(3, 0);
            }
            interpreter::push(stack_top, uint256_t{monad_vm_k});
            gas_remaining -= static_gas<traits, PUSH1>();
            instr_ptr += 2;
            if constexpr (HANDLER != nullptr) {
                MONAD_VM_MUST_TAIL return HANDLER(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top + 1,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
            else {
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top + 1,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
        else {
            static_assert(OP == ADD || OP == SHL || OP == SHR || OP == SAR);
            // The result replaces the top; the pair's net stack change is
            // zero. Its growth is PUSH1's, whose test push<1> has made where
            // the slots bring it here.
            static constexpr auto monad_vm_req = [] {
                auto r = fused_requirements<
                    traits,
                    PUSH1,
                    static_cast<compiler::EvmOpCode>(OP)>();
                if (has_slots<traits>) {
                    r.max_growth = 0;
                }
                return r;
            }();
            if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                gas_remaining += monad_vm_req.gas;
                MONAD_VM_CHECK(PUSH1);
                MONAD_VM_CHECK_AT(OP, 1);
            }
            uint256_t const monad_vm_imm{*(instr_ptr + 1)};
            if constexpr (OP == ADD) {
                // Without a carry out of the low word, the words above stay.
                uint64_t const monad_vm_low = (*stack_top)[0] + monad_vm_imm[0];
                if (MONAD_LIKELY(monad_vm_low >= monad_vm_imm[0])) {
                    (*stack_top)[0] = monad_vm_low;
                }
                else {
                    *stack_top = monad_vm_imm + *stack_top;
                }
            }
            else if constexpr (OP == SHL) {
                *stack_top <<= monad_vm_imm;
            }
            else if constexpr (OP == SHR) {
                *stack_top >>= monad_vm_imm;
            }
            else {
                *stack_top = sar(monad_vm_imm, *stack_top);
            }
            MONAD_VM_FUSED_NEXT(3, 0);
        }
    }

    // The word-by-word memory copy older Solidity compilers emit,
    //
    //     h: JUMPDEST DUP4 DUP2 LT ISZERO PUSH2 <end> JUMPI
    //        DUP2 DUP2 ADD MLOAD DUP4 DUP3 ADD MSTORE PUSH1 0x20 ADD
    //        PUSH2 <h> JUMP
    //
    // over [.. len dst src i]: a word a turn while i < len. The JUMPDEST
    // falling through into DUP4 DUP2 dispatches here, instr_ptr on the DUP4,
    // and the twin runs every turn at once from what the turns leave: the
    // memory grown to the furthest word, the words copied as the turns copy
    // them, i past len, and the gas of the turns and of the exit charged and
    // tested once, at the JUMPI that leaves -- a checkpoint (stack.hpp).
    // Whatever the fast path does not take -- another pattern, a word of 2^28
    // or more, growth past the capacity or the bound, the stack's last slots
    // -- runs the opcodes one by one. A loop entered by a jump to h runs them
    // one by one too: its JUMPDEST is swallowed.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void copy_loop(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const *const p = instr_ptr;
        auto const monad_vm_is = [p](size_t const k, auto const op) {
            return p[k] == static_cast<std::uint8_t>(op);
        };
        auto const monad_vm_small = [](uint256_t const &x) {
            return (x[1] | x[2] | x[3]) == 0 && x[0] < (uint64_t{1} << 28);
        };
        size_t const monad_vm_end = detail::load_be_k<2>(p + 5);
        size_t const monad_vm_head = detail::load_be_k<2>(p + 20);
        uint256_t const &monad_vm_i = stack_top[0];
        uint256_t const &monad_vm_src = stack_top[-1];
        uint256_t const &monad_vm_dst = stack_top[-2];
        uint256_t const &monad_vm_len = stack_top[-3];
        // The JUMPDEST before p is h, a JUMPDEST by its own dispatch.
        if (!(monad_vm_is(2, LT) && monad_vm_is(3, ISZERO) &&
              monad_vm_is(4, PUSH2) && monad_vm_is(7, JUMPI) &&
              monad_vm_is(8, DUP2) && monad_vm_is(9, DUP2) &&
              monad_vm_is(10, ADD) && monad_vm_is(11, MLOAD) &&
              monad_vm_is(12, DUP4) && monad_vm_is(13, DUP3) &&
              monad_vm_is(14, ADD) && monad_vm_is(15, MSTORE) &&
              monad_vm_is(16, PUSH1) && p[17] == 0x20 && monad_vm_is(18, ADD) &&
              monad_vm_is(19, PUSH2) && monad_vm_is(22, JUMP) &&
              monad_vm_head ==
                  static_cast<size_t>(p - 1 - MONAD_VM_ANALYSIS.code()) &&
              stack_top - 3 >= stack_bottom &&
              stack_top + 3 <= MONAD_VM_STACK_LIMIT &&
              monad_vm_small(monad_vm_len) && monad_vm_small(monad_vm_i) &&
              monad_vm_small(monad_vm_src) && monad_vm_small(monad_vm_dst) &&
              monad_vm_i[0] < monad_vm_len[0])) {
            MONAD_VM_DISPATCH(0, 0, *instr_ptr);
        }

        uint64_t const monad_vm_first = monad_vm_i[0];
        uint64_t const monad_vm_s = monad_vm_src[0];
        uint64_t const monad_vm_d = monad_vm_dst[0];
        uint64_t const monad_vm_turns =
            (monad_vm_len[0] - monad_vm_first + 31) >> 5;
        uint64_t const monad_vm_last =
            monad_vm_first + 32 * (monad_vm_turns - 1);
        // The furthest words' offsets are MLOAD's and MSTORE's: under 2^28.
        if (monad_vm_s + monad_vm_last >= (uint64_t{1} << 28) ||
            monad_vm_d + monad_vm_last >= (uint64_t{1} << 28)) {
            MONAD_VM_DISPATCH(0, 0, *instr_ptr);
        }
        uint64_t const monad_vm_far =
            std::max(monad_vm_s, monad_vm_d) + monad_vm_last + 32;
        int64_t monad_vm_expansion = 0;
        if (monad_vm_far > ctx.memory.size) {
            auto const monad_vm_words =
                runtime::Context::memory_size_to_word_count(
                    runtime::Bin<29>::unsafe_from(monad_vm_far));
            auto const monad_vm_size =
                runtime::Context::word_count_to_memory_size(monad_vm_words);
            if (MONAD_UNLIKELY(
                    ctx.memory.capacity < *monad_vm_size ||
                    !ctx.is_memory_size_in_bound<traits>(monad_vm_size))) {
                MONAD_VM_DISPATCH(0, 0, *instr_ptr);
            }
            auto const monad_vm_cost =
                runtime::Context::memory_cost_from_word_count<traits>(
                    monad_vm_words);
            monad_vm_expansion = monad_vm_cost - ctx.memory.cost;
            ctx.memory.size = *monad_vm_size;
            ctx.memory.cost = monad_vm_cost;
        }
        // A turn from the head's DUP4 to the next head, and the exit.
        static constexpr int64_t monad_vm_turn_gas = static_gas<
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
        static constexpr int64_t monad_vm_exit_gas = static_gas<
            traits,
            DUP4,
            DUP2,
            LT,
            ISZERO,
            PUSH2,
            JUMPI,
            JUMPDEST>();
        gas_remaining -=
            monad_vm_turn_gas * static_cast<int64_t>(monad_vm_turns) +
            monad_vm_exit_gas + monad_vm_expansion;
        if (MONAD_UNLIKELY(!MONAD_VM_ANALYSIS.is_jumpdest16(monad_vm_end))) {
            MONAD_VM_MUST_TAIL return ctx.exit(Error);
        }
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        uint8_t *const monad_vm_mem = ctx.memory.data;
        uint64_t const monad_vm_bytes = 32 * monad_vm_turns;
        // The turns read no word an earlier one wrote when the ranges are
        // apart: one copy. Otherwise word by word, in their order.
        if (monad_vm_d + monad_vm_bytes <= monad_vm_s ||
            monad_vm_s + monad_vm_bytes <= monad_vm_d) {
            std::memcpy(
                monad_vm_mem + monad_vm_d + monad_vm_first,
                monad_vm_mem + monad_vm_s + monad_vm_first,
                monad_vm_bytes);
        }
        else {
            for (uint64_t k = monad_vm_first; k <= monad_vm_last; k += 32) {
                uint64_t monad_vm_word[4];
                std::memcpy(monad_vm_word, monad_vm_mem + monad_vm_s + k, 32);
                std::memcpy(monad_vm_mem + monad_vm_d + k, monad_vm_word, 32);
            }
        }
        // i past len, where the exit's LT finds it.
        stack_top[0] = uint256_t{monad_vm_last + 32};
        instr_ptr = MONAD_VM_ANALYSIS.code() + monad_vm_end + 1;
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // The end of Solidity's finalize_allocation,
    //
    //     PUSH8 0xffffffffffffffff DUP3 GT OR PUSH2 <panic> JUMPI
    //     PUSH1 0x40 MSTORE JUMP
    //
    // over [.. ret ptr wrapped]: the new free memory pointer stored and a
    // return to ret, unless the pointer wrapped or passes 2^64 - 1, which
    // panics. push<8> tail-calls it when DUP3 follows the PUSH8. A panic, a
    // memory without its first three words, a return to no JUMPDEST and any
    // other pattern run the opcodes one by one, from this PUSH8.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push8_alloc(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const *const p = instr_ptr;
        auto const monad_vm_is = [p](size_t const k, auto const op) {
            return p[k] == static_cast<std::uint8_t>(op);
        };
        uint256_t const &monad_vm_wrapped = stack_top[0];
        uint256_t const &monad_vm_ptr = stack_top[-1];
        uint256_t const &monad_vm_ret = stack_top[-2];
        uint64_t monad_vm_imm;
        std::memcpy(&monad_vm_imm, p + 1, sizeof(monad_vm_imm));
        auto const monad_vm_dst = static_cast<size_t>(monad_vm_ret[0]);
        if (!(monad_vm_imm == ~uint64_t{0} && monad_vm_is(10, GT) &&
              monad_vm_is(11, OR) && monad_vm_is(12, PUSH2) &&
              monad_vm_is(15, JUMPI) && monad_vm_is(16, PUSH1) &&
              p[17] == 0x40 && monad_vm_is(18, MSTORE) &&
              monad_vm_is(19, JUMP) && stack_top - 2 >= stack_bottom &&
              stack_top + 2 <= MONAD_VM_STACK_LIMIT &&
              (monad_vm_wrapped[0] | monad_vm_wrapped[1] | monad_vm_wrapped[2] |
               monad_vm_wrapped[3]) == 0 &&
              (monad_vm_ptr[1] | monad_vm_ptr[2] | monad_vm_ptr[3]) == 0 &&
              ctx.memory.size >= 0x60 &&
              (monad_vm_ret[1] | monad_vm_ret[2] | monad_vm_ret[3]) == 0 &&
              MONAD_VM_ANALYSIS.is_jumpdest(monad_vm_dst))) {
            // The PUSH8 as push<8> runs it: dispatched to, it would call
            // this twin again.
            MONAD_VM_CHECK(PUSH8);
            push_impl<8, traits>::push(stack_top, instr_ptr);
            MONAD_VM_NEXT_PUSH(PUSH8);
        }
        static constexpr int64_t monad_vm_gas = static_gas<
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
        gas_remaining -= monad_vm_gas;
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        runtime::mstore_at<base_traits<traits>>(
            &ctx, runtime::Memory::Offset::unsafe_from(0x40), &monad_vm_ptr);
        instr_ptr = MONAD_VM_ANALYSIS.code() + monad_vm_dst + 1;
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top - 3,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // PUSH4 <mask> AND and PUSH20 <mask> AND, which Solidity cleans a
    // selector and an address with: the immediate applied to the top in
    // place, without the push. Apart from push<N>: in it the arm's
    // temporaries take a0, a1 and a6, which every PUSH4 and PUSH20 would
    // then copy away at its first instruction.
    template <size_t N, Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push_and(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        static constexpr auto monad_vm_req = fused_requirements<
            traits,
            static_cast<compiler::EvmOpCode>(PUSH0 + N),
            AND>();
        if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(PUSH0 + N);
            MONAD_VM_CHECK_AT(AND, 1);
        }
        auto &monad_vm_x = *stack_top;
        if constexpr (N == 4) {
            monad_vm_x[0] &= detail::load_be_k<4>(instr_ptr + 1);
            monad_vm_x[1] = 0;
            monad_vm_x[2] = 0;
            monad_vm_x[3] = 0;
        }
        else {
            static_assert(N == 20);
            monad_vm_x[0] &= detail::read_unaligned(instr_ptr + 13);
            monad_vm_x[1] &= detail::read_unaligned(instr_ptr + 5);
            monad_vm_x[2] &= detail::load_be_k<4>(instr_ptr + 1);
            monad_vm_x[3] = 0;
        }
        MONAD_VM_FUSED_NEXT(N + 2, 0);
    }

    // PUSH2 <dst> JUMP and PUSH2 <dst> JUMPI, one twin each: use the immediate
    // directly as the destination. Check gas and stack in opcode order, then
    // validate taken jumps. push<2> tail-calls the one its follower names.
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void push2_jump_at(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        // Decode PUSH2's destination with the shared big-endian reader
        // to favor the cheaper packh sequence on ZisK.
        auto const monad_vm_dst =
            static_cast<size_t>(detail::load_be_k<2>(instr_ptr + 1));
        // With the JUMPDEST that a valid destination is.
        static constexpr auto monad_vm_req =
            fused_requirements<traits, PUSH2, JUMP, JUMPDEST>();
        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(monad_vm_req))) {
            if (MONAD_UNLIKELY(
                    !MONAD_VM_ANALYSIS.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            instr_ptr = MONAD_VM_ANALYSIS.code() + monad_vm_dst + 1;
            // Formed where it is born: gcc would otherwise copy the
            // destination into a5 first, to add the base to it there.
            MONAD_VM_LAUNDER(instr_ptr);
        }
        else {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(PUSH2);
            // PUSH2 supplies the operand required by JUMP.
            MONAD_DEBUG_ASSERT(
                stack_top >= stack_bottom - MONAD_VM_STACK_BOTTOM_BIAS);
            MONAD_VM_CHARGE(JUMP);
            if (MONAD_UNLIKELY(
                    !MONAD_VM_ANALYSIS.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            instr_ptr = swallow_jumpdest(
                ctx, MONAD_VM_ANALYSIS.code() + monad_vm_dst, gas_remaining);
        }
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void push2_jumpi_at(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        auto const monad_vm_dst =
            static_cast<size_t>(detail::load_be_k<2>(instr_ptr + 1));
        static constexpr auto monad_vm_reqi =
            fused_requirements<traits, PUSH2, JUMPI>();
        if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_reqi))) {
            gas_remaining += monad_vm_reqi.gas;
            MONAD_VM_CHECK(PUSH2);
            MONAD_VM_CHECK_AT(JUMPI, 1);
        }
        // The charge made here, for both arms: folded into the taken arm's
        // JUMPDEST charge, it would cost the other arm a move.
        MONAD_VM_LAUNDER(gas_remaining);
        // The condition is the original top, below PUSH2's destination.
        if (*stack_top) {
            if (MONAD_UNLIKELY(
                    !MONAD_VM_ANALYSIS.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            auto const *monad_vm_ip = MONAD_VM_ANALYSIS.code() + monad_vm_dst;
            monad_vm_ip = swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
            instr_ptr = monad_vm_ip;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
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

    // PUSH2 and the opcode after its immediate, OP, as one: where the slots
    // compile it into JUMP's and JUMPI's (execute.cpp), PUSH2's head jumps
    // here, instr_ptr on the PUSH2.
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void push2_then(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        static_assert(OP == JUMP || OP == JUMPI || OP == MLOAD || OP == MSTORE);
        if constexpr (OP == MLOAD || OP == MSTORE) {
            // As push1_then's, the offset two bytes: PUSH2's stack test,
            // then the memory's size alone; outside it, the push and the
            // follower's handler.
            if (MONAD_UNLIKELY(stack_top >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            auto const monad_vm_k = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(
                    detail::load_be_k<2>(instr_ptr + 1)));
            if constexpr (OP == MLOAD) {
                if (MONAD_LIKELY(ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH2, MLOAD>();
                    runtime::mload_at<base_traits<traits>>(
                        &ctx, stack_top + 1, monad_vm_k);
                    MONAD_VM_FUSED_NEXT(4, 1);
                }
            }
            else {
                if (MONAD_LIKELY(
                        stack_top >= stack_bottom &&
                        ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH2, MSTORE>();
                    runtime::mstore_at<base_traits<traits>>(
                        &ctx, monad_vm_k, stack_top);
                    MONAD_VM_FUSED_NEXT(4, -1);
                }
            }
            interpreter::push(stack_top, uint256_t{*monad_vm_k});
            gas_remaining -= static_gas<traits, PUSH2>();
            instr_ptr += 3;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == JUMP) {
            MONAD_VM_MUST_TAIL return push2_jump_at<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else {
            MONAD_VM_MUST_TAIL return push2_jumpi_at<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    // The two as functions of their own, for push<2> where the slots do not
    // compile them into JUMP's and JUMPI's.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push2_jump(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        MONAD_VM_MUST_TAIL return push2_jump_at<traits>(
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push2_jumpi(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        MONAD_VM_MUST_TAIL return push2_jumpi_at<traits>(
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }
#endif

    template <size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Use PUSH1's immediate directly for ADD/SHL/SHR/SAR.
        // The result replaces the top; the pair's net stack change is zero.
        // Check PUSH1 before its follower, including temporary stack growth.
        // Code padding makes the lookahead safe.
        // Reuse the next opcode for fusion checks and normal dispatch.
        [[maybe_unused]] uint8_t monad_vm_op2 = 0;
        if constexpr (N == 1 || N == 2 || N == 4 || N == 8 || N == 20) {
            monad_vm_op2 = *(instr_ptr + N + 1);
        }
        if constexpr (N == 1 && has_slots<traits>) {
            // PUSH1 lands at a head of its follower's slot, before the copy
            // its lag selects (lead_offset, execute.cpp): for most opcodes
            // the push itself, which falls into the handler, and for those
            // push1_then fuses with it a jump there. Neither the follower's
            // tests nor a dispatch of the push's own; only the stack's test
            // is made here, the push's gas charged at the head.
            if (MONAD_UNLIKELY(stack_top >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            MONAD_VM_LEAD_DISPATCH(
                lead_offset(lag_of<traits>, 1),
                monad_vm_op2,
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>);
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
            if (monad_vm_op2 < 64 &&
                ((monad_vm_fuse_mask >> monad_vm_op2) & 1)) {
                // These four followers share gas and stack requirements.
                // Verify that ADD's checks cover all four.
                static constexpr auto monad_vm_req =
                    fused_requirements<traits, PUSH1, ADD>();
                static_assert(
                    monad_vm_req == fused_requirements<traits, PUSH1, SHL>() &&
                        monad_vm_req ==
                            fused_requirements<traits, PUSH1, SHR>() &&
                        monad_vm_req ==
                            fused_requirements<traits, PUSH1, SAR>(),
                    "PUSH1 fusion mask holds followers with unequal "
                    "requirements; aggregate them per follower");
                if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                    gas_remaining += monad_vm_req.gas;
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
                    MONAD_VM_MUST_TAIL return push1_shr<traits>(
                        ctx,
                        MONAD_VM_ANALYSIS_ARG,
                        stack_bottom,
                        stack_top,
                        gas_remaining,
                        MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
                }
                else {
                    MONAD_VM_MUST_TAIL return push1_sar<traits>(
                        ctx,
                        MONAD_VM_ANALYSIS_ARG,
                        stack_bottom,
                        stack_top,
                        gas_remaining,
                        MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
                }
                // Advance instr_ptr by 3 bytes, keep the stack size unchanged,
                // and call the next opcode handler.
                // Returns from the current handler.
                MONAD_VM_FUSED_NEXT(3, 0);
            }
            // PUSH1 <a> PUSH1 <b>, tested outside of the previous mask
            // because PUSH1 is #96 > 64.
            if (monad_vm_op2 == static_cast<std::uint8_t>(PUSH1)) {
                MONAD_VM_MUST_TAIL return push1_then<PUSH1, traits>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
        if constexpr (N == 2 && has_slots<traits>) {
            // PUSH2 lands as PUSH1 does, at a head of its own in its
            // follower's slot (execute.cpp): the stack's test and the push
            // there, and for JUMP and JUMPI a jump to their pair.
            MONAD_VM_LEAD_DISPATCH(
                lead_offset(lag_of<traits>, 2),
                monad_vm_op2,
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>);
        }
        // PUSH2 JUMP and PUSH2 JUMPI run in twins of their own: their arms
        // want a0 and a6 for temporaries, and inlined here they would make
        // every PUSH2 copy ctx and the table away at its first instruction.
        if constexpr (N == 2) {
            // Match JUMP and JUMPI with one range check: they are consecutive.
            // size_t and not unsigned for the difference: a 32-bit subtract
            // puts this on ZisK's generic binary machine on every PUSH2.
            auto const monad_vm_jump =
                static_cast<size_t>(monad_vm_op2) - static_cast<size_t>(JUMP);
            if (monad_vm_jump <= 1u) {
                if (monad_vm_jump == 0) {
                    MONAD_VM_MUST_TAIL return push2_jump<traits>(
                        ctx,
                        MONAD_VM_ANALYSIS_ARG,
                        stack_bottom,
                        stack_top,
                        gas_remaining,
                        MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
                }
                MONAD_VM_MUST_TAIL return push2_jumpi<traits>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
        }
        if constexpr (N == 2) {
            // Held in a5 through an empty asm, so gcc does not take a5 for
            // the stack limit's load and copy instr_ptr away for it.
            MONAD_VM_LAUNDER(instr_ptr);
        }
        // PUSH8 DUP3 may end finalize_allocation: its twin tells.
        if constexpr (N == 8) {
            if (monad_vm_op2 == static_cast<std::uint8_t>(DUP3)) {
                MONAD_VM_MUST_TAIL return push8_alloc<traits>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
        }
        // PUSH4 <mask> AND and PUSH20 <mask> AND in their twin.
        if constexpr (N == 4 || N == 20) {
            if (monad_vm_op2 == static_cast<std::uint8_t>(AND)) {
                MONAD_VM_MUST_TAIL return push_and<N, traits>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
        }
#endif
        MONAD_VM_CHECK(PUSH0 + N);
        push_impl<N, traits>::push(stack_top, instr_ptr);

#if defined(MONAD_ZKVM_ZISK)
        if constexpr (N == 1 || N == 2 || N == 4 || N == 8 || N == 20) {
            MONAD_VM_NEXT_PUSH_OP(PUSH0 + N, monad_vm_op2);
        }
#endif
        MONAD_VM_NEXT_PUSH(PUSH0 + N);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(POP);
        MONAD_VM_NEXT(POP);
    }

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Fuse DUP1 PUSH4 <selector> EQ PUSH2 <dst> JUMPI without temporary
        // stack writes. Fusing only DUP1/PUSH4/EQ would prevent the existing
        // EQ/PUSH2/JUMPI fusion.
        // Keep the next opcode for the unfused path to avoid reloading it.
        [[maybe_unused]] uint8_t monad_vm_op2 = 0;
        if constexpr (N == 1) {
            monad_vm_op2 = *(instr_ptr + 1);
            // Check PUSH4 first; Intercode's tail padding makes lookahead
            // through instr_ptr[10] safe. A stack without the word DUP1
            // copies, or the room for the two the sequence pushes, halts as
            // DUP1 or PUSH4 would: the charge leaves gas to JUMPI, and every
            // exceptional halt is the same to the block.
            if (monad_vm_op2 == static_cast<std::uint8_t>(PUSH4) &&
                *(instr_ptr + 6) == static_cast<std::uint8_t>(EQ) &&
                *(instr_ptr + 7) == static_cast<std::uint8_t>(PUSH2) &&
                *(instr_ptr + 10) == static_cast<std::uint8_t>(JUMPI)) {
                static constexpr auto monad_vm_req =
                    fused_requirements<traits, DUP1, PUSH4, EQ, PUSH2, JUMPI>();
                if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                    MONAD_VM_MUST_TAIL return ctx.exit(Error);
                }
                // The charge made here, as in push2_jumpi.
                MONAD_VM_LAUNDER(gas_remaining);
                // A contract's function dispatch is a chain of these tests,
                // one a selector. The stack is the same before each of them,
                // so a test not taken goes on to the next without a dispatch
                // or the stack's tests; the tail padding keeps the lookahead
                // past a test that ends the code in bounds.
                while (uint256_t{detail::load_be_k<4>(instr_ptr + 2)} !=
                       *stack_top) {
                    instr_ptr += 11;
                    if (*instr_ptr != static_cast<std::uint8_t>(DUP1) ||
                        *(instr_ptr + 1) != static_cast<std::uint8_t>(PUSH4) ||
                        *(instr_ptr + 6) != static_cast<std::uint8_t>(EQ) ||
                        *(instr_ptr + 7) != static_cast<std::uint8_t>(PUSH2) ||
                        *(instr_ptr + 10) != static_cast<std::uint8_t>(JUMPI)) {
                        MONAD_VM_DISPATCH(0, 0, *instr_ptr);
                    }
                    gas_remaining -= monad_vm_req.gas;
                }
                // fused_branch expects a pointer to EQ, followed by
                // PUSH2 <dst> JUMPI.
                instr_ptr =
                    fused_branch(ctx, instr_ptr + 6, true, gas_remaining);
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
            // The dispatch's binary search: DUP1 PUSH4 <pivot> GT PUSH2 <dst>
            // JUMPI, taken when the selector is below the pivot.
            if (monad_vm_op2 == static_cast<std::uint8_t>(PUSH4) &&
                *(instr_ptr + 6) == static_cast<std::uint8_t>(GT) &&
                *(instr_ptr + 7) == static_cast<std::uint8_t>(PUSH2) &&
                *(instr_ptr + 10) == static_cast<std::uint8_t>(JUMPI)) {
                static constexpr auto monad_vm_req =
                    fused_requirements<traits, DUP1, PUSH4, GT, PUSH2, JUMPI>();
                if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                    MONAD_VM_MUST_TAIL return ctx.exit(Error);
                }
                MONAD_VM_LAUNDER(gas_remaining);
                bool const monad_vm_taken =
                    (uint256_t{detail::load_be_k<4>(instr_ptr + 2)} >
                     *stack_top);
                instr_ptr = fused_branch(
                    ctx, instr_ptr + 6, monad_vm_taken, gas_remaining);
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top,
                    gas_remaining,
                    instr_ptr MONAD_VM_TBL_ARG);
            }
        }
#endif
#if defined(MONAD_ZKVM_ZISK)
        if constexpr (N == 1) {
            MONAD_VM_CHECK(DUP1);

            auto *const old_top = stack_top;
            push(stack_top, *old_top);

            MONAD_VM_NEXT_OP(DUP1, monad_vm_op2);
        }
        else {
            MONAD_VM_CHECK_OWN_OVERFLOW(DUP1 + (N - 1));
            if constexpr (has_slots<traits>) {
                // DUPn lands at a head of its follower's slot, as SWAP1 does,
                // with the address of the word it copies: the copy there and
                // a jump to the handler, or the pair it makes with ADD, AND,
                // LT, GT or MSTORE (execute.cpp).
                MONAD_VM_LEAD_DISPATCH_SRC(
                    dup_offset(lag_of<traits>),
                    *(instr_ptr + 1),
                    stack_top,
                    gas_remaining,
                    instr_ptr - lag_of<traits>,
                    stack_top - (N - 1));
            }

            // The copy's destination is the new top: step there first, so the
            // register the copy writes through is the one the dispatch passes
            // on, not a second one moved into place after it. Its source is
            // the deepest operand, whose address the underflow test formed.
            auto const *const source = stack_top - (N - 1);
            ++stack_top;
            MONAD_VM_LAUNDER(stack_top);
            *stack_top = *source;

            MONAD_VM_DISPATCH(1, 0, *instr_ptr);
        }
#else
        MONAD_VM_CHECK(DUP1 + (N - 1));

        auto *const old_top = stack_top;
        push(stack_top, *(old_top - (N - 1)));

        MONAD_VM_NEXT(DUP1 + (N - 1));
#endif
    }

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(SWAP1 + (N - 1));

#if defined(MONAD_ZKVM_ZISK)
        if constexpr (N >= 2 && has_slots<traits>) {
            // SWAPn lands at a head of its follower's slot as the DUPs do,
            // the word the top swaps with in a7: the swap there and a jump
            // to the handler, or the pair it makes with POP or SWAP1 to
            // SWAP4 (execute.cpp).
            MONAD_VM_LEAD_DISPATCH_SRC(
                swapn_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                stack_top - N);
        }
        if constexpr (N == 1 && has_slots<traits>) {
            // SWAP1 lands at a head of its follower's slot, as PUSH1 does:
            // the swap there and a jump to the handler, or the pair it makes
            // with POP or JUMP (execute.cpp). Only the stack's test and the
            // gas are made here.
            MONAD_VM_LEAD_DISPATCH(
                swap1_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top,
                gas_remaining,
                instr_ptr - lag_of<traits>);
        }

        // Reuse Context's scratch slot to avoid a local 32-byte stack frame.
        {
            uint256_t *const monad_t = &ctx.swap_scratch;
            *monad_t = *stack_top;
            *stack_top = *(stack_top - N);
            *(stack_top - N) = *monad_t;
        }
#else
        // Keep the temporary as uint256_t to avoid an AVX round trip.
        uint256_t const top = *stack_top;
        *stack_top = *(stack_top - N);
        *(stack_top - N) = top;
#endif

        MONAD_VM_NEXT(SWAP1 + (N - 1));
    }

    // Control Flow
    namespace
    {
        template <typename Analysis>
        inline uint8_t const *jump_impl(
            runtime::Context &ctx, Analysis const &analysis,
            uint256_t const &target)
        {
            // Our bytecode offsets use 64-bit size_t; EVM targets are 256-bit.
            // Reject nonzero upper words before narrowing, avoiding a full
            // uint256_t comparison. is_jumpdest checks bounds and JUMPDEST.
            if (MONAD_UNLIKELY((target[1] | target[2] | target[3]) != 0)) {
                ctx.exit(Error);
            }

            auto const jd = static_cast<size_t>(target[0]);
            if (MONAD_UNLIKELY(!analysis.is_jumpdest(jd))) {
                ctx.exit(Error);
            }

            return analysis.code() + jd;
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // With the JUMPDEST that a valid destination is.
        static constexpr auto monad_vm_req =
            fused_requirements<traits, JUMP, JUMPDEST>();
        uint8_t const *new_ip;
        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(monad_vm_req))) {
            auto const &target = pop(stack_top);
            new_ip = jump_impl(ctx, MONAD_VM_ANALYSIS, target) + 1;
        }
        else {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(JUMP);
            auto const &target = pop(stack_top);
            new_ip = swallow_jumpdest(
                ctx, jump_impl(ctx, MONAD_VM_ANALYSIS, target), gas_remaining);
        }
#else
        MONAD_VM_CHECK(JUMP);
        auto const &target = pop(stack_top);
        auto const *new_ip = jump_impl(ctx, MONAD_VM_ANALYSIS, target);
#endif

        if constexpr (debug_enabled) {
            trace(MONAD_VM_ANALYSIS, gas_remaining, new_ip);
        }
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            new_ip MONAD_VM_TBL_ARG);
    }

#if defined(MONAD_ZKVM_ZISK)
    // SWAP1 JUMP, SWAP1's test and gas made: the destination is the word
    // under the top, and the top takes its place.
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swap1_jump(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_PARAM)
    {
        static constexpr auto monad_vm_req =
            fused_requirements<traits, JUMP, JUMPDEST>();
        uint8_t const *new_ip;
        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(monad_vm_req))) {
            new_ip = jump_impl(ctx, MONAD_VM_ANALYSIS, *(stack_top - 1)) + 1;
        }
        else {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(JUMP);
            new_ip = swallow_jumpdest(
                ctx,
                jump_impl(ctx, MONAD_VM_ANALYSIS, *(stack_top - 1)),
                gas_remaining);
        }
        *(stack_top - 1) = *stack_top;
        --stack_top;
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            new_ip MONAD_VM_TBL_ARG);
    }

    // SWAP1 then DUP2 or SWAP2, SWAP1's test and gas made: a b -> b a b in
    // three copies where the two opcodes make four, x y z -> y z x in four
    // where they make six.
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swap1_then(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        if constexpr (OP == DUP2) {
            MONAD_VM_CHECK_OWN_OVERFLOW(DUP2);
            stack_top[1] = stack_top[0];
            stack_top[0] = stack_top[-1];
            stack_top[-1] = stack_top[1];
            ++stack_top;
        }
        else {
            static_assert(OP == SWAP2);
            MONAD_VM_CHECK(SWAP2);
            uint256_t *const monad_t = &ctx.swap_scratch;
            *monad_t = stack_top[-2];
            stack_top[-2] = stack_top[-1];
            stack_top[-1] = stack_top[0];
            stack_top[0] = *monad_t;
        }
        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
    }

    // SWAPn then SWAPm, SWAPn's tests and gas made, the word the top swaps
    // with at SRC: the top's word goes to SRC, SRC's to the m-th below the
    // top and that one's to the top, four copies where the two opcodes make
    // six. When m is n they leave the stack as it was, as the two opcodes do.
    // SWAP1 and SWAP2 swap words SWAPn has tested, n being 2 or more.
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swapn_then(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint256_t *const src)
    {
        static constexpr auto op = static_cast<compiler::EvmOpCode>(OP);
        constexpr auto m = static_cast<std::ptrdiff_t>(OP - SWAP1 + 1);
        if constexpr (m <= 2) {
            gas_remaining -= static_gas<traits, op>();
        }
        else {
            MONAD_VM_CHECK(op);
        }
        uint256_t *const monad_t = &ctx.swap_scratch;
        *monad_t = *src;
        *src = *stack_top;
        *stack_top = *(stack_top - m);
        *(stack_top - m) = *monad_t;
        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
    }

    // bool_push2 without a JUMPI after the push: the result written, then
    // PUSH2. Out of line, so that bool_push2 keeps its arguments where its
    // own dispatch wants them instead of copies for this arm.
    template <Traits traits>
    [[gnu::noinline]] void bool_push2_write(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint64_t const bit)
    {
        *stack_top = uint256_t{bit};
        MONAD_VM_MUST_TAIL return push<2, traits>(
            ctx,
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    // A comparison then PUSH2, its result BIT not yet written to the top: with
    // JUMPI after the push, the branch on BIT as push2_jumpi_at makes it on the
    // top; otherwise the result written and PUSH2. The result's slot is there,
    // the comparison's own test made, so PUSH2's room is the only test left.
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void bool_push2(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint64_t const bit)
    {
        if (MONAD_UNLIKELY(*(instr_ptr + 3) != static_cast<uint8_t>(JUMPI))) {
            MONAD_VM_MUST_TAIL return bool_push2_write<traits>(
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG,
                bit);
        }
        auto const monad_vm_dst =
            static_cast<size_t>(detail::load_be_k<2>(instr_ptr + 1));
        if (MONAD_UNLIKELY(stack_top >= MONAD_VM_STACK_LIMIT)) {
            MONAD_VM_MUST_TAIL return ctx.exit(Error);
        }
        gas_remaining -= static_gas<traits, PUSH2, JUMPI>();
        MONAD_VM_LAUNDER(gas_remaining);
        if (bit) {
            if (MONAD_UNLIKELY(
                    !MONAD_VM_ANALYSIS.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            auto const *monad_vm_ip = MONAD_VM_ANALYSIS.code() + monad_vm_dst;
            monad_vm_ip = swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
            instr_ptr = monad_vm_ip;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top - 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        MONAD_VM_FUSED_NEXT(4, -1);
    }

    // A comparison then OR, its result BIT not yet written: the bit ORed into
    // the low word of the operand under it.
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void bool_or(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint64_t const bit)
    {
        MONAD_VM_CHECK(OR);
        (*(stack_top - 1))[0] |= bit;
        MONAD_VM_DISPATCH(1, -1, *instr_ptr);
    }

    // DUPn then ADD, SUB, AND, LT, GT, MLOAD, MSTORE or SWAP1, DUPn's tests
    // and gas made: the word DUPn copies, at SRC, is read where it lies
    // instead of copied to the top. A load or a store that grows the memory
    // makes the copy and takes its opcode's growth path; LT's and GT's result
    // goes to the follower's head in a7, as LT's does.
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void dup_then(
        runtime::Context &entry_ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint256_t const *const src)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        if constexpr (OP == MSTORE) {
            MONAD_VM_CHECK_OWN_GAS(MSTORE);
            auto const offset = ctx.get_memory_offset(*src);
            if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
                *(stack_top + 1) = *src;
                MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top + 1,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            runtime::mstore_at<base_traits<traits>>(&ctx, offset, stack_top);
            MONAD_VM_DISPATCH(1, -1, *instr_ptr);
        }
        else if constexpr (OP == MLOAD) {
            MONAD_VM_CHECK_OWN_GAS(MLOAD);
            auto const offset = ctx.get_memory_offset(*src);
            if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
                *(stack_top + 1) = *src;
                MONAD_VM_MUST_TAIL return mload_grow<quiet_traits<traits>>(
                    ctx,
                    MONAD_VM_ANALYSIS_ARG,
                    stack_bottom,
                    stack_top + 1,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            runtime::mload_at<base_traits<traits>>(&ctx, stack_top + 1, offset);
            MONAD_VM_DISPATCH(1, 1, *instr_ptr);
        }
        else if constexpr (OP == SWAP1) {
            // The old top one slot up, the copied word under it.
            gas_remaining -= static_gas<traits, SWAP1>();
            *(stack_top + 1) = *stack_top;
            *stack_top = *src;
            MONAD_VM_DISPATCH(1, 1, *instr_ptr);
        }
        else {
            gas_remaining -=
                static_gas<traits, static_cast<compiler::EvmOpCode>(OP)>();
            if constexpr (OP == ADD) {
                ctx.add256_params.a = reinterpret_cast<uint64_t const *>(src);
                zisk_add256(ctx.add256_params, *stack_top, *stack_top);
            }
            else if constexpr (OP == SUB) {
                // As SUB: the copied word less the top, into the top.
                ctx.sub256_params.a = reinterpret_cast<uint64_t const *>(src);
                asm volatile("" ::: "memory");
                auto &b = *stack_top;
                for (size_t i = 0; i < 4; ++i) {
                    b[i] = ~b[i];
                }
                zisk_add256(ctx.sub256_params, b, b);
            }
            else if constexpr (OP == LT || OP == GT) {
                // The result goes on to the follower's head in a7.
                bool const monad_vm_bit =
                    OP == LT ? *src < *stack_top : *src > *stack_top;
                MONAD_VM_LEAD_DISPATCH_BIT(
                    bool_offset(lag_of<traits>),
                    *(instr_ptr + 1),
                    stack_top,
                    gas_remaining,
                    instr_ptr - lag_of<traits>,
                    static_cast<uint64_t>(monad_vm_bit));
            }
            else {
                static_assert(OP == AND);
                *stack_top = *src & *stack_top;
            }
            MONAD_VM_DISPATCH(1, 0, *instr_ptr);
        }
    }
#endif

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK(JUMPI);
        auto const &target = pop(stack_top);
        auto const &cond = pop(stack_top);

        if (cond) {
            auto const *new_ip = jump_impl(ctx, MONAD_VM_ANALYSIS, target);
#if defined(MONAD_ZKVM_ZISK)
            new_ip = swallow_jumpdest(ctx, new_ip, gas_remaining);
#endif
            if constexpr (debug_enabled) {
                trace(MONAD_VM_ANALYSIS, gas_remaining, new_ip);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                new_ip MONAD_VM_TBL_ARG);
        }
        else {
            ++instr_ptr;
            if constexpr (debug_enabled) {
                trace(MONAD_VM_ANALYSIS, gas_remaining, instr_ptr);
            }
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_ANALYSIS_ARG,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        fuzz_tstore_stack(
            ctx,
            stack_bottom,
            stack_top,
            static_cast<uint64_t>(instr_ptr - MONAD_VM_ANALYSIS.code()));
        MONAD_VM_CHECK(JUMPDEST);

#if defined(MONAD_ZKVM_ZISK)
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
            MONAD_VM_ANALYSIS_ARG,
            stack_bottom,
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
    log(runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        static constexpr auto impls = std::tuple{
            &runtime::log0<base_traits<traits>>,
            &runtime::log1<base_traits<traits>>,
            &runtime::log2<base_traits<traits>>,
            &runtime::log3<base_traits<traits>>,
            &runtime::log4<base_traits<traits>>,
        };

        MONAD_VM_CHECKED_RUNTIME_CALL(LOG0 + N, std::get<N>(impls));

        MONAD_VM_NEXT(LOG0 + N);
    }

    // Call & Create
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CREATE, runtime::create<base_traits<traits>>);

        MONAD_VM_NEXT(CREATE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALL, runtime::call<base_traits<traits>>);

        MONAD_VM_NEXT(CALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CALLCODE, runtime::callcode<base_traits<traits>>);

        MONAD_VM_NEXT(CALLCODE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            DELEGATECALL, runtime::delegatecall<base_traits<traits>>);

        MONAD_VM_NEXT(DELEGATECALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CREATE2, runtime::create2<base_traits<traits>>);

        MONAD_VM_NEXT(CREATE2);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            STATICCALL, runtime::staticcall<base_traits<traits>>);

        MONAD_VM_NEXT(STATICCALL);
    }

    // VM Control
    namespace
    {
        // A handler's own exit. On ZisK it returns: every handler restores
        // the registers it saved before its tail call, so the chain returns to
        // the trampoline with the registers the trampoline saved, which a
        // longjmp would reload -- 13 of them, on every frame. An exit from
        // inside a runtime call still longjmps.
        inline void handler_exit(
            runtime::Context &ctx, runtime::StatusCode const code)
        {
#if defined(MONAD_ZKVM_ZISK)
            ctx.result.status = code;
#else
            ctx.exit(code);
#endif
        }

        inline void return_impl(
            runtime::StatusCode const code, runtime::Context &ctx,
            uint256_t *stack_top, int64_t const gas_remaining)
        {
#if defined(MONAD_ZKVM_ZISK)
            // The frame ends here: the count an earlier opcode left
            // negative is tested here (gas_tested).
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
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(
            ctx, stack_bottom, stack_top, MONAD_VM_ANALYSIS.size());
        MONAD_VM_CHECK(RETURN);
        return_impl(Success, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        MONAD_VM_CHECK(REVERT);
        return_impl(Revert, ctx, stack_top, gas_remaining);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *stack_bottom, uint256_t *stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        fuzz_tstore_stack(
            ctx, stack_bottom, stack_top, MONAD_VM_ANALYSIS.size());
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SELFDESTRUCT, runtime::selfdestruct<base_traits<traits>>);
    }

    MONAD_VM_INLINE_INSTRUCTION_CALL void stop(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_PARAM,
        uint256_t const *const stack_bottom, uint256_t *const stack_top,
        int64_t const gas_remaining, uint8_t const *MONAD_VM_TBL_TYPE)
    {
        fuzz_tstore_stack(
            ctx, stack_bottom, stack_top, MONAD_VM_ANALYSIS.size());
#if defined(MONAD_ZKVM_ZISK)
        // As in return_impl.
        if (MONAD_UNLIKELY(gas_remaining < 0)) {
            ctx.exit(OutOfGas);
        }
#endif
        ctx.gas_remaining = gas_remaining;
        handler_exit(ctx, Success);
    }

    MONAD_VM_INLINE_INSTRUCTION_CALL void invalid(
        runtime::Context &ctx, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
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
#undef MONAD_VM_NEXT_OP
#undef MONAD_VM_NEXT_PUSH
#undef MONAD_VM_NEXT_PUSH_OP
#undef MONAD_VM_CHECK
#undef MONAD_VM_CHECK_AT
#undef MONAD_VM_CHARGE
#undef MONAD_VM_FUSED_CHARGE
#undef MONAD_VM_FUSED_CHARGE_PURE
#undef MONAD_VM_CHECKED_RUNTIME_CALL
