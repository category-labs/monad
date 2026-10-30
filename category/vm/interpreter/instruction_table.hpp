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

#include <evmc/evmc.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
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
                                   STATICCALL,   DUPN,         SWAPN,
                                   EXCHANGE};
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
                MONAD_VM_DISPATCH_STATE_ARG;                                   \
            register uint256_t const *monad_vm_a2 asm("a2") =                  \
                stack_lower_bound;                                             \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP).next_slot();     \
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
                MONAD_VM_DISPATCH_STATE_ARG;                                   \
            register uint256_t const *monad_vm_a2 asm("a2") =                  \
                stack_lower_bound;                                             \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP).next_slot();     \
            register int64_t monad_vm_a4 asm("a4") = (GAS);                    \
            register uint8_t const *monad_vm_a5 asm("a5") = (IP);              \
            register void const *monad_vm_a6 asm("a6") = itbl;                 \
            register uint256_t const *monad_vm_a7 asm("a7") = &*(SRC);         \
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
                MONAD_VM_DISPATCH_STATE_ARG;                                   \
            register uint256_t const *monad_vm_a2 asm("a2") =                  \
                stack_lower_bound;                                             \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP).next_slot();     \
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
                MONAD_VM_DISPATCH_STATE_ARG;                                   \
            register uint256_t const *monad_vm_a2 asm("a2") =                  \
                stack_lower_bound;                                             \
            register uint256_t *monad_vm_a3 asm("a3") = (TOP).next_slot();     \
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
                    trace(MONAD_VM_CODE_VIEW, gas_remaining, instr_ptr);       \
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
                    trace(MONAD_VM_CODE_VIEW, gas_remaining, instr_ptr);       \
                }                                                              \
                MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[(NEXT_OPCODE)](   \
                    ctx,                                                       \
                    MONAD_VM_DISPATCH_STATE_ARG,                               \
                    stack_lower_bound,                                         \
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
                trace(MONAD_VM_CODE_VIEW, gas_remaining, instr_ptr);           \
            }                                                                  \
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[(NEXT_OPCODE)](       \
                ctx,                                                           \
                MONAD_VM_DISPATCH_STATE_ARG,                                   \
                stack_lower_bound,                                             \
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
#define MONAD_VM_NEXT_IMM(OP) MONAD_VM_NEXT_IMPL(OP, 2, *instr_ptr)

// Expand musttail in the handler to avoid return-address saves on the fast
// path. The guest exits via longjmp, so it does not need the handler's stack
// frame.
#define MONAD_VM_CHECK(OP) MONAD_VM_CHECK_AT(OP, 0)

// Keep checks in the handler so failures can tail-call Context::exit.
// Variadic to accept runtime functions with multiple template arguments.
#if defined(MONAD_ZKVM_ZISK)
// After a runtime function that takes the Context, a real call, the stack's
// bounds are read back from ctx: kept across it, each takes a saved register,
// stored, moved in and out and reloaded. The arithmetic ones are inlined.
    #define MONAD_VM_CHECKED_RUNTIME_CALL(OP, ...)                             \
        do {                                                                   \
            MONAD_VM_CHECK(OP);                                                \
            constexpr bool monad_vm_real_call =                                \
                ::monad::vm::interpreter::runtime_fn_uses_context<             \
                    std::decay_t<decltype(__VA_ARGS__)>>::value;               \
            if constexpr (monad_vm_real_call) {                                \
                ctx.frame_stack_top = stack_top.next_slot();                   \
            }                                                                  \
            call_runtime(__VA_ARGS__, ctx, stack_top, gas_remaining);          \
            if constexpr (monad_vm_real_call) {                                \
                stack_lower_bound = ctx.frame_stack_bottom;                    \
                stack_limit = ctx.stack_limit;                                 \
                stack_top = StackTop{ctx.frame_stack_top};                     \
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

    // Subtract first, then test the sign. Laundering prevents GCC from
    // replacing this with a comparison that needs another constant load.
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
    // cross into its neighbour move in one shift by 64 - b, as in uint256_t's
    // shifts: a zero b, which would make it a shift by 64, is taken apart in
    // the arms where words pass bits.
    [[gnu::always_inline]] inline void
    shr_in_place(uint256_t &x, uint64_t const k) noexcept
    {
        unsigned const b = static_cast<unsigned>(k & 63);
        unsigned const nb = 64 - b;
        switch (k >> 6) {
        case 0: {
            if (b == 0) {
                break;
            }
            uint64_t const x0 = x[0], x1 = x[1], x2 = x[2], x3 = x[3];
            x[0] = (x0 >> b) | (x1 << nb);
            x[1] = (x1 >> b) | (x2 << nb);
            x[2] = (x2 >> b) | (x3 << nb);
            x[3] = x3 >> b;
            break;
        }
        case 1: {
            uint64_t const x1 = x[1], x2 = x[2], x3 = x[3];
            if (b == 0) {
                x[0] = x1;
                x[1] = x2;
                x[2] = x3;
            }
            else {
                x[0] = (x1 >> b) | (x2 << nb);
                x[1] = (x2 >> b) | (x3 << nb);
                x[2] = x3 >> b;
            }
            x[3] = 0;
            break;
        }
        case 2: {
            uint64_t const x2 = x[2], x3 = x[3];
            if (b == 0) {
                x[0] = x2;
                x[1] = x3;
            }
            else {
                x[0] = (x2 >> b) | (x3 << nb);
                x[1] = x3 >> b;
            }
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
        unsigned const nb = 64 - b;
        switch (k >> 6) {
        case 0: {
            if (b == 0) {
                break;
            }
            uint64_t const x0 = x[0], x1 = x[1], x2 = x[2], x3 = x[3];
            x[3] = (x3 << b) | (x2 >> nb);
            x[2] = (x2 << b) | (x1 >> nb);
            x[1] = (x1 << b) | (x0 >> nb);
            x[0] = x0 << b;
            break;
        }
        case 1: {
            uint64_t const x0 = x[0], x1 = x[1], x2 = x[2];
            if (b == 0) {
                x[3] = x2;
                x[2] = x1;
                x[1] = x0;
            }
            else {
                x[3] = (x2 << b) | (x1 >> nb);
                x[2] = (x1 << b) | (x0 >> nb);
                x[1] = x0 << b;
            }
            x[0] = 0;
            break;
        }
        case 2: {
            uint64_t const x0 = x[0], x1 = x[1];
            if (b == 0) {
                x[3] = x1;
                x[2] = x0;
            }
            else {
                x[3] = (x1 << b) | (x0 >> nb);
                x[2] = x0 << b;
            }
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
#if defined(MONAD_ZKVM_ZISK)
    // b = a - b, b's slot not a's. A subtrahend under 2^64 that a's low word
    // covers changes that word alone, the others a's own (3 SUBs in 4 on
    // 25815159); any other is complemented in place, from the words the test
    // loaded, and added to a by add256 with a carry-in of 1.
    [[gnu::always_inline]] inline void zisk_sub256_into(
        runtime::Context &ctx, uint64_t const *const a, uint256_t &b)
    {
        uint64_t const b0 = b[0];
        uint64_t const b1 = b[1];
        uint64_t const b2 = b[2];
        uint64_t const b3 = b[3];
        if ((b1 | b2 | b3) == 0 && a[0] >= b0) {
            uint64_t const lo = a[0] - b0;
            b[1] = a[1];
            b[2] = a[2];
            b[3] = a[3];
            b[0] = lo;
            return;
        }
        ctx.sub256_params.a = a;
        b[0] = ~b0;
        b[1] = ~b1;
        b[2] = ~b2;
        b[3] = ~b3;
        zisk_add256(ctx.sub256_params, b, b);
    }
#endif

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
        // Name a, then step to the new top, as ADD does.
        uint64_t const *const a =
            reinterpret_cast<uint64_t const *>(&*stack_top);
        --stack_top;
        auto *next_slot = stack_top.next_slot();
        MONAD_VM_LAUNDER(next_slot);
        stack_top = StackTop{next_slot};
        zisk_sub256_into(ctx, a, *stack_top);

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
#if defined(MONAD_ZKVM_ZISK)
        MONAD_VM_CHECK(EXP);
        {
            // A power of two 2^s, s >= 1, to an exponent below 256, the byte
            // shift older Solidity compiles to EXP (base 256), is 2^(s·e), or
            // 0 past the word. Here, in the handler: the runtime call that
            // takes every other power copies the base and the result through
            // the stack around a call to exp(), some 110 steps.
            uint256_t const &monad_vm_base = *stack_top;
            uint256_t const &monad_vm_e = *(stack_top - 1);
            uint64_t const monad_vm_b = monad_vm_base[0];
            if ((monad_vm_base[1] | monad_vm_base[2] | monad_vm_base[3] |
                 monad_vm_e[1] | monad_vm_e[2] | monad_vm_e[3]) == 0 &&
                monad_vm_b > 1 && (monad_vm_b & (monad_vm_b - 1)) == 0 &&
                monad_vm_e[0] < 256) {
                // The dynamic gas, per byte of the exponent: one byte or none.
                if (monad_vm_e[0] != 0) {
                    gas_remaining -=
                        runtime::exp_dynamic_gas_cost_multiplier<traits>();
                    if (MONAD_UNLIKELY(gas_remaining < 0)) {
                        MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
                    }
                }
                uint64_t const monad_vm_shift =
                    static_cast<uint64_t>(std::countr_zero(monad_vm_b)) *
                    monad_vm_e[0];
                auto &&[a, b] = top_two(stack_top);
                (void)a;
                // The one bit written into its word, the others zero.
                b = uint256_t{0};
                if (monad_vm_shift < 256) {
                    b[monad_vm_shift >> 6] = uint64_t{1}
                                             << (monad_vm_shift & 63);
                }
                MONAD_VM_NEXT(EXP);
            }
        }
        call_runtime(
            runtime::exp<base_traits<traits>>, ctx, stack_top, gas_remaining);
#else
        MONAD_VM_CHECKED_RUNTIME_CALL(EXP, runtime::exp<base_traits<traits>>);
#endif

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
    eq(runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
       uint256_t const *stack_lower_bound, StackTop stack_top,
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
                    (stack_top.next_slot() - 1) -
                        (stack_lower_bound - MONAD_VM_STACK_LOWER_BOUND_BIAS) <
                    static_cast<std::ptrdiff_t>(
                        runtime::EvmStackAllocatorMeta::stack_limit));
                MONAD_VM_CHARGE(PUSH2);
                // PUSH2 adds one value, restoring the original stack height.
                MONAD_VM_CHECK_AT(JUMPI, 0);
            }
            // Keep EQ's result in a C++ bool instead of the EVM stack, the
            // words compared by DMA (zisk_equal32): one step where gcc's
            // compare is three a word, and half of EQ's run all four.
            bool const monad_vm_taken = zisk_equal32(
                reinterpret_cast<uint64_t const *>(&*(stack_top)),
                reinterpret_cast<uint64_t const *>(&*(stack_top - 1)));
            instr_ptr =
                fused_branch(ctx, instr_ptr, monad_vm_taken, gas_remaining);
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
                    reinterpret_cast<uint64_t const *>(&*(stack_top)),
                    reinterpret_cast<uint64_t const *>(&*(stack_top - 1)))));
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
#if defined(MONAD_ZKVM_ZISK)
    // SHA3 past runtime::sha3_memo, out of line so that a hash the memo
    // holds takes no frame. The checks have run; do not repeat them.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void sha3_hash(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        call_runtime(
            runtime::sha3<base_traits<traits>>, ctx, stack_top, gas_remaining);

        MONAD_VM_NEXT(SHA3);
    }

    // The 32 or 64 bytes sha3 found inside the memory but not in the memo:
    // hashed and kept, their gas charged.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void sha3_fill(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        uint64_t const n = stack_top[-1][0];
        auto const *const in = reinterpret_cast<uint64_t const *>(
            ctx.memory.data + stack_top[0][0]);
        if (n == 64) {
            runtime::sha3_memo_fill<64>(in, &stack_top[-1]);
        }
        else {
            runtime::sha3_memo_fill<32>(in, &stack_top[-1]);
        }
        gas_remaining -= static_cast<int64_t>((n >> 4) * 3);

        MONAD_VM_NEXT(SHA3);
    }

#endif
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sha3(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        MONAD_VM_CHECK(SHA3);
        // 32 or 64 bytes at an 8-aligned offset inside the memory, with their
        // words of gas: the memo's word if it holds them, else sha3_fill.
        // Anything else goes through sha3_hash. (n - 32) & ~32 is zero for
        // the two sizes alone.
        uint256_t const &offset = stack_top[0];
        uint256_t const &size = stack_top[-1];
        uint64_t const n = size[0];
        uint64_t const o = offset[0];
        uint64_t const end = ctx.memory_access32_end;
        int64_t const gas = static_cast<int64_t>((n >> 4) * 3);
        if (MONAD_UNLIKELY(
                (((n - 32) & ~uint64_t{32}) | size[1] | size[2] | size[3]) !=
                    0 ||
                ((o & 7) | offset[1] | offset[2] | offset[3]) != 0 ||
                o >= end || o + 32 >= end || gas_remaining < gas)) {
            MONAD_VM_MUST_TAIL return sha3_hash<quiet_traits<traits>>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        auto const *const in =
            reinterpret_cast<uint64_t const *>(ctx.memory.data + o);
        uint256_t const *word;
        if (n == 64) {
            auto const &e = runtime::sha3_memo_entry<64>(in);
            word = runtime::sha3_memo_holds(e, in) ? &e.out : nullptr;
        }
        else {
            auto const &e = runtime::sha3_memo_entry<32>(in);
            word = runtime::sha3_memo_holds(e, in) ? &e.out : nullptr;
        }
        if (MONAD_UNLIKELY(word == nullptr)) {
            MONAD_VM_MUST_TAIL return sha3_fill<quiet_traits<traits>>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        gas_remaining -= gas;
        stack_top[-1] = *word;

        MONAD_VM_NEXT(SHA3);
#else
        MONAD_VM_CHECKED_RUNTIME_CALL(SHA3, runtime::sha3<base_traits<traits>>);

        MONAD_VM_NEXT(SHA3);
#endif
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
        MONAD_VM_CHECKED_RUNTIME_CALL(
            BALANCE, runtime::balance<base_traits<traits>>);

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
        if (push0 && traits::evm_rev() < MONAD_ETH_SHANGHAI) {
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
        MONAD_VM_TWIN_ENTRY();
        auto const *const instructions = instr_ptr;
        alignas(8) static constexpr uint8_t push0_tail[8] = {
            JUMPI, PUSH0, DUP1, REVERT, JUMPDEST, POP};
        alignas(8) static constexpr uint8_t push1_tail[8] = {
            JUMPI, PUSH1, 0, DUP1, REVERT, JUMPDEST, POP};
        // PUSH0 occupies one byte less than PUSH1 0, shifting the success
        // label.
        size_t success_offset;
        bool matches_revert_tail;
        if (opcode_at_is(instructions, 7, PUSH0)) {
            success_offset = 10;
            matches_revert_tail = code_matches<6>(instructions + 6, push0_tail);
        }
        else {
            success_offset = 11;
            matches_revert_tail = code_matches<7>(instructions + 6, push1_tail);
        }
        size_t const jump_destination = detail::load_be_k<2>(instructions + 4);
        size_t const instruction_offset =
            static_cast<size_t>(instructions - MONAD_VM_CODE_VIEW.code());
        // The full pattern proves this destination is a JUMPDEST instruction,
        // so no bitmap lookup is needed.
        if (MONAD_UNLIKELY(!(
                matches_revert_tail && opcode_at_is(instructions, 2, ISZERO) &&
                opcode_at_is(instructions, 3, PUSH2) &&
                jump_destination == instruction_offset + success_offset &&
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
        MONAD_VM_TWIN_ENTRY();
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
        size_t const bound_length =
            ir_bound_length<traits>(ctx, instructions + 5);
        if (bound_length != 0) {
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
        instr_ptr += 5 + bound_length;
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
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        if (instr_ptr[1] == static_cast<std::uint8_t>(PUSH2)) {
            MONAD_VM_MUST_TAIL return callvalue_ir<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        MONAD_VM_CHECK(CALLDATALOAD);
        // CALLDATALOAD reads the environment but never changes gas.
        runtime::calldataload(&ctx, &*stack_top, &*stack_top);

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
        if (traits::evm_rev() >= MONAD_ETH_SHANGHAI &&
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
        MONAD_VM_TWIN_ENTRY();
        alignas(8) static constexpr uint8_t taken_prefix_pattern[8] = {
            static_cast<uint8_t>(ISZERO), static_cast<uint8_t>(PUSH2)};
        auto const *const instructions = instr_ptr;
        bool const falls_through = opcode_at_is(instructions, 2, PUSH2) &&
                                   opcode_at_is(instructions, 5, JUMPI);
        bool const jumps_to_dispatch =
            code_matches<2>(instructions + 2, taken_prefix_pattern) &&
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
        MONAD_VM_TWIN_ENTRY();
        alignas(8) static constexpr uint8_t bound_pattern[8] = {
            static_cast<uint8_t>(DUP2),
            static_cast<uint8_t>(LT),
            static_cast<uint8_t>(ISZERO),
            static_cast<uint8_t>(PUSH2)};
        auto const *const instructions = instr_ptr;
        uint64_t const calldata_size = ctx.env.input_data_size;
        if (MONAD_UNLIKELY(
                !(opcode_at_is(instructions, 2, PUSH1) &&
                  code_matches<4>(instructions + 4, bound_pattern) &&
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
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        if (instr_ptr[1] == static_cast<std::uint8_t>(SUB)) {
            MONAD_VM_MUST_TAIL return calldata_bound<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CALLDATACOPY, runtime::calldatacopy<base_traits<traits>>);

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
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CODECOPY, runtime::codecopy<base_traits<traits>>);

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
            EXTCODESIZE, runtime::extcodesize<base_traits<traits>>);

        MONAD_VM_NEXT(EXTCODESIZE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODECOPY, runtime::extcodecopy<base_traits<traits>>);

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
            RETURNDATACOPY, runtime::returndatacopy<base_traits<traits>>);

        MONAD_VM_NEXT(RETURNDATACOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            EXTCODEHASH, runtime::extcodehash<base_traits<traits>>);

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
        MONAD_VM_TWIN_ENTRY();
        call_runtime(
            runtime::mload<base_traits<traits>>, ctx, stack_top, gas_remaining);

        MONAD_VM_NEXT(MLOAD);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECK_OWN_GAS(MLOAD);

        // No gas sync: only the growth path charges, and mload_grow syncs
        // through call_runtime. An out-of-range offset exits OutOfGas, whose
        // result carries no gas.
#if defined(MONAD_ZKVM_ZISK)
        // High words zero and a low word under memory_access32_end: inside
        // the memory. A low word from there up, growth or an offset out of
        // range, goes through mload_grow's generic path. The high words exit
        // on their own: a second branch to mload_grow keeps all its arguments
        // live, and gcc copies them away into a frame.
        uint256_t const &monad_vm_x = *stack_top;
        if (MONAD_UNLIKELY(
                (monad_vm_x[1] | monad_vm_x[2] | monad_vm_x[3]) != 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        if (MONAD_UNLIKELY(monad_vm_x[0] >= ctx.memory_access32_end)) {
            MONAD_VM_MUST_TAIL return mload_grow<quiet_traits<traits>>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        auto const offset = runtime::Memory::Offset::unsafe_from(
            static_cast<runtime::Memory::Offset::rep>(monad_vm_x[0]));
#else
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mload_grow<quiet_traits<traits>>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
#endif
        runtime::mload_at<base_traits<traits>>(&ctx, &*stack_top, offset);

        MONAD_VM_NEXT(MLOAD);
    }

    // What mstore_grow does not take, through the generic path: capacity
    // growth, an offset of 2^28 or more (on ZisK, any from memory_grow_end
    // up), and a size past the transaction's memory limit.
    template <Traits traits>
    [[gnu::noinline, gnu::cold]] MONAD_VM_TWIN_CALL void mstore_slow(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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

    // Expand within the allocated capacity and charge the local gas counter.
    // Tail calls keep allocation off this path.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void mstore_grow(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        // mstore validated the offset's high words, so its low word is all
        // of it; on the host it is also under 2^28, on ZisK it is bounded
        // here.
#if defined(MONAD_ZKVM_ZISK)
        // A low word under memory_grow_end is under 2^28, and its store grows
        // the memory within the capacity. One from there up, past the
        // capacity or out of range, goes through the generic path, before
        // it is made a Memory::Offset, which must be under 2^28.
        if (MONAD_UNLIKELY((*stack_top)[0] >= ctx.memory_grow_end)) {
            MONAD_VM_MUST_TAIL return mstore_slow<quiet_traits<traits>>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
#endif
        auto const offset = runtime::Memory::Offset::unsafe_from(
            static_cast<runtime::Memory::Offset::rep>((*stack_top)[0]));
        auto const word_count = runtime::Context::memory_size_to_word_count(
            offset + runtime::bin<32>);
        auto const new_size =
            runtime::Context::word_count_to_memory_size(word_count);
#if defined(MONAD_ZKVM_ZISK)
        // The bound above stood for the capacity test.
        MONAD_DEBUG_ASSERT(*new_size <= ctx.memory.capacity);
        bool const monad_vm_beyond = false;
#else
        bool const monad_vm_beyond = ctx.memory.capacity < *new_size;
#endif
        if (MONAD_UNLIKELY(
                monad_vm_beyond ||
                !ctx.is_memory_size_in_bound<traits>(new_size))) {
            MONAD_VM_MUST_TAIL return mstore_slow<quiet_traits<traits>>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
#if defined(MONAD_ZKVM_ZISK)
        ctx.memory_access32_end = *new_size - 31;
#endif
        ctx.memory.cost = new_cost;
        runtime::mstore_at<base_traits<traits>>(&ctx, offset, &stack_top[-1]);

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
        MONAD_VM_LAUNDER_AS_CALLED(instr_ptr);
        MONAD_VM_CHECK_OWN_GAS(MSTORE);

        // A store inside the memory charges nothing, so no gas sync, and it
        // makes no call, so no frame.
#if defined(MONAD_ZKVM_ZISK)
        // As in mload: high words zero and a low word under
        // memory_access32_end. A low word from there up grows the memory,
        // and mstore_grow bounds it: one of 2^28 or more goes through the
        // generic path, which runs out of gas.
        uint256_t const &monad_vm_x = *stack_top;
        if (MONAD_UNLIKELY(
                (monad_vm_x[1] | monad_vm_x[2] | monad_vm_x[3]) != 0)) {
            MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
        }
        if (MONAD_UNLIKELY(monad_vm_x[0] >= ctx.memory_access32_end)) {
            MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
        auto const offset = runtime::Memory::Offset::unsafe_from(
            static_cast<runtime::Memory::Offset::rep>(monad_vm_x[0]));
#else
        auto const offset = ctx.get_memory_offset(*stack_top);
        if (MONAD_UNLIKELY(ctx.memory.size < *offset + 32)) {
            MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
        }
#endif
        runtime::mstore_at<base_traits<traits>>(&ctx, offset, &stack_top[-1]);

        MONAD_VM_NEXT(MSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            MSTORE8, runtime::mstore8<base_traits<traits>>);

        MONAD_VM_NEXT(MSTORE8);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            MCOPY, runtime::mcopy<base_traits<traits>>);

        MONAD_VM_NEXT(MCOPY);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SSTORE, runtime::sstore<base_traits<traits>>);

        MONAD_VM_NEXT(SSTORE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SLOAD, runtime::sload<base_traits<traits>>);

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
        MONAD_VM_TWIN_ENTRY();
        *stack_top >>= uint256_t{*(instr_ptr + 1)};
        MONAD_VM_FUSED_NEXT(3, 0);
    }

    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push1_sar(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        auto const monad_vm_k = static_cast<size_t>(*(instr_ptr + 1));
        // k / 64 selects the boundary word; its low k % 64 bits are ones.
        // Lower words are all ones, and higher words are zero.
        size_t const monad_vm_w = monad_vm_k >> 6;
        uint64_t const monad_vm_low = (uint64_t{1} << (monad_vm_k & 63)) - 1;
        if (*(instr_ptr + 4) == static_cast<std::uint8_t>(AND)) {
            // Apply the mask directly to x, below the two ones.
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
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        // MSTORE's pairs keep ctx in a0: see their arm.
        runtime::Context &ctx = [&]() -> runtime::Context & {
            if constexpr (OP == MSTORE) {
                return held_in_a0(entry_ctx);
            }
            else {
                return entry_ctx;
            }
        }();
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
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top + 2,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            interpreter::push(stack_top, uint256_t{monad_vm_imm1});
            if (MONAD_UNLIKELY(
                    stack_top.next_slot() + 1 >= MONAD_VM_STACK_LIMIT)) {
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
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top + 2,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == MLOAD || OP == MSTORE) {
            if constexpr (OP == MSTORE) {
                // The arguments laundered where they came, ctx at the top:
                // the fallback, most of the calls (the preamble's PUSH1 0x80
                // PUSH1 0x40 MSTORE grows the memory), passes them on, and
                // gcc otherwise frees a0, a1, a2, a5 and a6 for the fast arm
                // with a copy of each at entry and copies them back before
                // the jump. Not MLOAD's, which falls back far less.
                MONAD_VM_LAUNDER(MONAD_VM_DISPATCH_STATE_ARG);
                MONAD_VM_LAUNDER(stack_lower_bound);
                MONAD_VM_LAUNDER(itbl);
            }
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
                        &ctx, &stack_top[1], monad_vm_k);
                    MONAD_VM_FUSED_NEXT(3, 1);
                }
            }
            else {
                // MSTORE's value is the top.
                if (MONAD_LIKELY(
                        stack_holds<1>(stack_top, stack_lower_bound) &&
                        ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH1, MSTORE>();
                    runtime::mstore_at<base_traits<traits>>(
                        &ctx, monad_vm_k, &*stack_top);
                    MONAD_VM_FUSED_NEXT(3, -1);
                }
            }
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
        else if constexpr (OP >= SWAP1 && OP <= SWAP4) {
            // The word n below the top moves up to where the push would put
            // the immediate, and the immediate takes its place.
            constexpr size_t monad_vm_n = OP - SWAP1 + 1;
            uint8_t const monad_vm_k = *(instr_ptr + 1);
            if (MONAD_LIKELY(
                    stack_holds<monad_vm_n>(stack_top, stack_lower_bound))) {
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
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
            if (MONAD_LIKELY(stack_holds<1>(stack_top, stack_lower_bound))) {
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
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
            if (MONAD_LIKELY(
                    stack_holds<1>(stack_top, stack_lower_bound) &&
                    monad_vm_k < 31)) {
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
    #if defined(MONAD_ZKVM_ZISK)
                // By the immediate's range, each with its own exit: through
                // one exit, gcc built the four words in registers, the zeros
                // too, and jumped to their stores, and the general shift's
                // callee-saved register put a frame around every shift.
                uint64_t const monad_vm_k = monad_vm_imm[0];
                unsigned const monad_vm_b = monad_vm_k & 63;
                auto &monad_vm_x = *stack_top;
                if (monad_vm_k >= 192) {
                    monad_vm_x[0] = monad_vm_x[3] >> monad_vm_b;
                    monad_vm_x[1] = 0;
                    monad_vm_x[2] = 0;
                    monad_vm_x[3] = 0;
                    MONAD_VM_FUSED_NEXT(3, 0);
                }
                if (monad_vm_k >= 128) {
                    uint64_t const monad_vm_hi = monad_vm_x[3];
                    // hi << (64 - b) in two shifts, so that b = 0 shifts
                    // nothing in rather than by 64.
                    monad_vm_x[0] = (monad_vm_x[2] >> monad_vm_b) |
                                    ((monad_vm_hi << 1) << (63 - monad_vm_b));
                    monad_vm_x[1] = monad_vm_hi >> monad_vm_b;
                    monad_vm_x[2] = 0;
                    monad_vm_x[3] = 0;
                    MONAD_VM_FUSED_NEXT(3, 0);
                }
                *stack_top >>= monad_vm_imm;
                MONAD_VM_FUSED_NEXT(3, 0);
    #else
                *stack_top >>= monad_vm_imm;
    #endif
            }
            else {
                *stack_top = sar(monad_vm_imm, *stack_top);
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
        ctx.memory_access32_end =
            new_memory_size >= 32 ? new_memory_size - 31 : 0;
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
        MONAD_VM_TWIN_ENTRY();
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
        runtime::mstore_at<base_traits<traits>>(
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

    #if defined(MONAD_ZKVM_ZISK)
    // Twenty ones, aligned, for push_and's address mask.
    alignas(8) inline constexpr unsigned char twenty_ones[24] = {
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};

    // Whether the 20 bytes at p are all ones, by the DMA comparator (CSR
    // 0x814, the length in the flag after it).
    [[gnu::always_inline]] inline bool
    twenty_ones_at(uint8_t const *const p) noexcept
    {
        uint64_t differ;
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "addi x0, %2, 20\n\t"
            ".option pop"
            : "=&r"(differ)
            : "r"(p),
              "r"(twenty_ones),
              "m"(*reinterpret_cast<uint8_t const(*)[20]>(p)),
              "m"(twenty_ones));
        return differ == 0;
    }

    #endif
    // PUSH4 <mask> AND and PUSH20 <mask> AND, which Solidity cleans a
    // selector and an address with: the immediate applied to the top in
    // place, without the push. Apart from push<N>: in it the arm's
    // temporaries take a0, a1 and a6, which every PUSH4 and PUSH20 would
    // then copy away at its first instruction.
    template <size_t N, Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push_and(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
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
    #if defined(MONAD_ZKVM_ZISK)
            // The address mask, twenty ones, as Solidity nearly always
            // writes it: the AND clears the top twelve bytes. Comparing the
            // immediate with the DMA comparator costs less than the three
            // unaligned reads that apply any other.
            if (MONAD_LIKELY(twenty_ones_at(instr_ptr + 1))) {
                monad_vm_x[2] &= 0xffffffffu;
                monad_vm_x[3] = 0;
                MONAD_VM_FUSED_NEXT(N + 2, 0);
            }
    #endif
            monad_vm_x[0] &= detail::read_unaligned(instr_ptr + 13);
            monad_vm_x[1] &= detail::read_unaligned(instr_ptr + 5);
            monad_vm_x[2] &= detail::load_be_k<4>(instr_ptr + 1);
            monad_vm_x[3] = 0;
        }
        MONAD_VM_FUSED_NEXT(N + 2, 0);
    }

    // Separate handlers keep jump temporaries out of ordinary PUSH2 execution.
    // Use the immediate destination; preserve gas, stack and jump checks.
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void push2_jump_at(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        // Decode PUSH2's destination with the shared big-endian reader
        // to favor the cheaper packh sequence on ZisK.
        auto const monad_vm_dst =
            static_cast<size_t>(detail::load_be_k<2>(instr_ptr + 1));
        // Include the destination JUMPDEST in the upfront gas charge.
        static constexpr auto monad_vm_req =
            fused_requirements<traits, PUSH2, JUMP, JUMPDEST>();
        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(monad_vm_req))) {
            if (MONAD_UNLIKELY(
                    !MONAD_VM_CODE_VIEW.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            instr_ptr = MONAD_VM_CODE_VIEW.code() + monad_vm_dst + 1;
            // Discourage GCC from copying the destination before the add.
            MONAD_VM_LAUNDER(instr_ptr);
        }
        else {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(PUSH2);
            // PUSH2 supplies the operand required by JUMP.
            MONAD_DEBUG_ASSERT(
                stack_top.next_slot() >=
                stack_lower_bound - MONAD_VM_STACK_LOWER_BOUND_BIAS);
            MONAD_VM_CHARGE(JUMP);
            if (MONAD_UNLIKELY(
                    !MONAD_VM_CODE_VIEW.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            instr_ptr = swallow_jumpdest(
                ctx, MONAD_VM_CODE_VIEW.code() + monad_vm_dst, gas_remaining);
        }
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void push2_jumpi_at(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        static constexpr auto monad_vm_reqi =
            fused_requirements<traits, PUSH2, JUMPI>();
        if (MONAD_UNLIKELY(!MONAD_VM_FUSED_CHARGE_PURE(monad_vm_reqi))) {
            gas_remaining += monad_vm_reqi.gas;
            MONAD_VM_CHECK(PUSH2);
            MONAD_VM_CHECK_AT(JUMPI, 1);
        }
        // Keep the sequence's gas deduction before the branch to avoid
        // extra register moves when dispatching either outcome.
        MONAD_VM_LAUNDER(gas_remaining);
        // The condition is the original top, below PUSH2's destination.
        if (*stack_top) {
            // Decoded on this arm only: the other one never reads it.
            auto const monad_vm_dst =
                static_cast<size_t>(detail::load_be_k<2>(instr_ptr + 1));
            if (MONAD_UNLIKELY(
                    !MONAD_VM_CODE_VIEW.is_jumpdest16(monad_vm_dst))) {
                ctx.exit(Error);
            }
            auto const *monad_vm_ip = MONAD_VM_CODE_VIEW.code() + monad_vm_dst;
            monad_vm_ip = swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
            instr_ptr = monad_vm_ip;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top - 1, // Consume JUMPI's condition.
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        // Skip the pair and consume the condition when the jump is not taken.
        MONAD_VM_FUSED_NEXT(4, -1);
    }

    // PUSH2 and the opcode after its immediate, OP, as one: where the slots
    // compile it into JUMP's and JUMPI's (execute.cpp), PUSH2's head jumps
    // here, instr_ptr on the PUSH2.
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void push2_then(
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        static_assert(OP == JUMP || OP == JUMPI || OP == MLOAD || OP == MSTORE);
        // MSTORE's pairs keep ctx in a0, as push1_then's.
        runtime::Context &ctx = [&]() -> runtime::Context & {
            if constexpr (OP == MSTORE) {
                return held_in_a0(entry_ctx);
            }
            else {
                return entry_ctx;
            }
        }();
        if constexpr (OP == MLOAD || OP == MSTORE) {
            if constexpr (OP == MSTORE) {
                // As push1_then's: the arguments where they came.
                MONAD_VM_LAUNDER(MONAD_VM_DISPATCH_STATE_ARG);
                MONAD_VM_LAUNDER(stack_lower_bound);
                MONAD_VM_LAUNDER(itbl);
            }
            // As push1_then's, the offset two bytes: PUSH2's stack test,
            // then the memory's size alone; outside it, the push and the
            // follower's handler.
            if (MONAD_UNLIKELY(stack_top.next_slot() >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            auto const monad_vm_k = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(
                    detail::load_be_k<2>(instr_ptr + 1)));
            if constexpr (OP == MLOAD) {
                if (MONAD_LIKELY(ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH2, MLOAD>();
                    runtime::mload_at<base_traits<traits>>(
                        &ctx, &stack_top[1], monad_vm_k);
                    MONAD_VM_FUSED_NEXT(4, 1);
                }
            }
            else {
                if (MONAD_LIKELY(
                        stack_holds<1>(stack_top, stack_lower_bound) &&
                        ctx.memory.size >= *monad_vm_k + 32)) {
                    gas_remaining -= static_gas<traits, PUSH2, MSTORE>();
                    runtime::mstore_at<base_traits<traits>>(
                        &ctx, monad_vm_k, &*stack_top);
                    MONAD_VM_FUSED_NEXT(4, -1);
                }
            }
            interpreter::push(stack_top, uint256_t{*monad_vm_k});
            gas_remaining -= static_gas<traits, PUSH2>();
            instr_ptr += 3;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[OP](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top + 1,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else if constexpr (OP == JUMP) {
            MONAD_VM_MUST_TAIL return push2_jump_at<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
        else {
            MONAD_VM_MUST_TAIL return push2_jumpi_at<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG);
        }
    }

    // The two as functions of their own, for push<2> where the slots do not
    // compile them into JUMP's and JUMPI's.
    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push2_jump(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        MONAD_VM_MUST_TAIL return push2_jump_at<traits>(
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
    }

    template <Traits traits>
    [[gnu::noinline]] MONAD_VM_TWIN_CALL void push2_jumpi(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_TWIN_ENTRY();
        MONAD_VM_MUST_TAIL return push2_jumpi_at<traits>(
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            instr_ptr MONAD_VM_TBL_ARG);
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
            if (MONAD_UNLIKELY(stack_top.next_slot() >= MONAD_VM_STACK_LIMIT)) {
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
                        MONAD_VM_DISPATCH_STATE_ARG,
                        stack_lower_bound,
                        stack_top,
                        gas_remaining,
                        MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
                }
                else {
                    MONAD_VM_MUST_TAIL return push1_sar<traits>(
                        ctx,
                        MONAD_VM_DISPATCH_STATE_ARG,
                        stack_lower_bound,
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
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
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
                        MONAD_VM_DISPATCH_STATE_ARG,
                        stack_lower_bound,
                        stack_top,
                        gas_remaining,
                        MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
                }
                MONAD_VM_MUST_TAIL return push2_jumpi<traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            // Encourage GCC to retain instr_ptr while checking the stack limit.
            MONAD_VM_LAUNDER(instr_ptr);
        }
        // Check the full allocation suffix in a separate helper.
    #if !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
        if constexpr (N == 8) {
            if (monad_vm_op2 == static_cast<std::uint8_t>(DUP3)) {
                MONAD_VM_MUST_TAIL return push8_alloc<traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
        }
    #endif
        // PUSH4 <mask> AND and PUSH20 <mask> AND in their twin.
        if constexpr (N == 4 || N == 20) {
            if (monad_vm_op2 == static_cast<std::uint8_t>(AND)) {
                MONAD_VM_MUST_TAIL return push_and<N, traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
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
        [[maybe_unused]] uint8_t monad_vm_op2 = 0;
        if constexpr (N == 1) {
            monad_vm_op2 = *(instr_ptr + 1);
            // Check PUSH4 first; Intercode's tail padding makes lookahead
            // through instr_ptr[10] safe. A stack without the word DUP1
            // copies, or the room for the two the sequence pushes, halts as
            // DUP1 or PUSH4 would: the charge leaves gas to JUMPI, and every
            // exceptional halt is the same to the block.
            // Two tests take this form, the dispatch's selector chain with EQ
            // and its binary search with GT, and both end on one branch.
            uint8_t const monad_vm_op6 = *(instr_ptr + 6);
            if (monad_vm_op2 == static_cast<std::uint8_t>(PUSH4) &&
                *(instr_ptr + 7) == static_cast<std::uint8_t>(PUSH2) &&
                *(instr_ptr + 10) == static_cast<std::uint8_t>(JUMPI) &&
                (monad_vm_op6 == static_cast<std::uint8_t>(EQ) ||
                 monad_vm_op6 == static_cast<std::uint8_t>(GT))) {
                bool monad_vm_taken = true;
                if (monad_vm_op6 == static_cast<std::uint8_t>(EQ)) {
                    static constexpr auto monad_vm_req = fused_requirements<
                        traits,
                        DUP1,
                        PUSH4,
                        EQ,
                        PUSH2,
                        JUMPI>();
                    if (MONAD_UNLIKELY(
                            !MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                        MONAD_VM_MUST_TAIL return ctx.exit(Error);
                    }
                    // The charge made here, as in push2_jumpi.
                    MONAD_VM_LAUNDER(gas_remaining);
                    // A contract's function dispatch is a chain of these
                    // tests, one a selector. The stack is the same before each
                    // of them, so a test not taken goes on to the next without
                    // a dispatch or the stack's tests; the tail padding keeps
                    // the lookahead past a test that ends the code in bounds.
                    //
                    // A test's first eight bytes, DUP1 PUSH4 <selector> EQ
                    // PUSH2, are one unaligned word: the test matches when the
                    // word is the one the selector makes, its bytes 2 to 5 the
                    // selector's read big-endian, and the chain goes on while a
                    // word has the frame's four bytes and JUMPI follows three
                    // bytes on. Five byte reads and the selector's swap a test
                    // become one load, one compare and the frame's. A selector
                    // that does not fit four bytes matches none: the word it
                    // wants is zero, and a test's word starts with DUP1.
                    uint64_t monad_vm_frame =
                        uint64_t{static_cast<std::uint8_t>(DUP1)} |
                        uint64_t{static_cast<std::uint8_t>(PUSH4)} << 8 |
                        uint64_t{static_cast<std::uint8_t>(EQ)} << 48 |
                        uint64_t{static_cast<std::uint8_t>(PUSH2)} << 56;
                    // Built once, for the word wanted and the chain's test.
                    MONAD_VM_LAUNDER(monad_vm_frame);
                    auto const test_word = [](uint8_t const *const p) {
                        uint64_t w;
                        asm("ld %0, %1"
                            : "=r"(w)
                            : "m"(*reinterpret_cast<uint8_t const(*)[8]>(p)));
                        return w;
                    };
                    uint256_t const &monad_vm_sel = *stack_top;
                    uint64_t const monad_vm_want =
                        (monad_vm_sel[1] | monad_vm_sel[2] | monad_vm_sel[3] |
                         (monad_vm_sel[0] >> 32)) == 0
                            ? monad_vm_frame |
                                  uint64_t{__builtin_bswap32(
                                      static_cast<uint32_t>(monad_vm_sel[0]))}
                                      << 16
                            : 0;
                    uint64_t monad_vm_word = test_word(instr_ptr);
                    while (monad_vm_word != monad_vm_want) {
                        instr_ptr += 11;
                        monad_vm_word = test_word(instr_ptr);
                        if ((monad_vm_word & 0xffff'0000'0000'ffff) !=
                                monad_vm_frame ||
                            *(instr_ptr + 10) !=
                                static_cast<std::uint8_t>(JUMPI)) {
                            MONAD_VM_DISPATCH(0, 0, *instr_ptr);
                        }
    #if defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)
                        MONAD_VM_CHARGE(DUP1);
                        MONAD_VM_CHARGE(PUSH4);
                        MONAD_VM_CHARGE(EQ);
                        MONAD_VM_CHARGE(PUSH2);
                        MONAD_VM_CHARGE(JUMPI);
    #else
                        gas_remaining -= monad_vm_req.gas;
    #endif
                    }
                }
                else {
                    // The binary search: taken when the selector is below the
                    // pivot.
                    static constexpr auto monad_vm_req = fused_requirements<
                        traits,
                        DUP1,
                        PUSH4,
                        GT,
                        PUSH2,
                        JUMPI>();
                    if (MONAD_UNLIKELY(
                            !MONAD_VM_FUSED_CHARGE_PURE(monad_vm_req))) {
                        MONAD_VM_MUST_TAIL return ctx.exit(Error);
                    }
                    MONAD_VM_LAUNDER(gas_remaining);
                    monad_vm_taken =
                        (uint256_t{detail::load_be_k<4>(instr_ptr + 2)} >
                         *stack_top);
                }
                // fused_branch expects a pointer to EQ or GT, followed by
                // PUSH2 <dst> JUMPI.
                instr_ptr = fused_branch(
                    ctx, instr_ptr + 6, monad_vm_taken, gas_remaining);
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

            MONAD_VM_NEXT_OP(DUP1, monad_vm_op2);
        }
        else {
            MONAD_VM_CHECK_OWN_OVERFLOW(DUP1 + (N - 1));
            if constexpr (has_slots<traits>) {
                // DUPn lands at a head of its follower's slot, as SWAP1 does,
                // with the address of the word it copies: the copy there and
                // a jump to the handler, or the pair it makes with ADD, AND,
                // LT, GT, EQ, ISZERO, CALLDATALOAD or MSTORE, among others,
                // or the copy and PUSH1's or PUSH2's handler (execute.cpp).
                MONAD_VM_LEAD_DISPATCH_SRC(
                    dup_offset(lag_of<traits>),
                    *(instr_ptr + 1),
                    stack_top,
                    gas_remaining,
                    instr_ptr - lag_of<traits>,
                    stack_top - (N - 1));
            }

            // Advance the one-past pointer before copying, then reuse it for
            // dispatch. From the new top, the source is N slots below.
            auto *next = stack_top.next_slot() + 1;
            MONAD_VM_LAUNDER(next);
            stack_top = StackTop{next};
            *stack_top = stack_top[-N];

            MONAD_VM_DISPATCH(1, 0, *instr_ptr);
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
        if constexpr (N >= 2 && has_slots<traits>) {
            // SWAPn lands at a head of its follower's slot as the DUPs do,
            // the word the top swaps with in a7: the swap there and a jump
            // to the handler, or the pair it makes with POP, ADD, SUB, AND,
            // MSTORE or SWAP1 to SWAP4 (execute.cpp).
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_PARAM)
    {
#if defined(MONAD_ZKVM_ZISK)
        // Include the destination JUMPDEST in the upfront gas charge.
        static constexpr auto monad_vm_req =
            fused_requirements<traits, JUMP, JUMPDEST>();
        uint8_t const *new_ip;
        if (MONAD_LIKELY(MONAD_VM_FUSED_CHARGE(monad_vm_req))) {
            auto const &target = pop(stack_top);
            new_ip = jump_impl(ctx, MONAD_VM_CODE_VIEW, target) + 1;
        }
        else {
            gas_remaining += monad_vm_req.gas;
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

#if defined(MONAD_ZKVM_ZISK)
    // SWAP1 JUMP, SWAP1's test and gas made: the destination is the word
    // under the top, and the top takes its place.
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swap1_jump(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *MONAD_VM_TBL_PARAM)
    {
        static constexpr auto monad_vm_req =
            fused_requirements<traits, JUMP, JUMPDEST>();
        // SWAP1 tested two words, JUMP's one among them, and the jump does
        // not grow the stack: only the gas is left to test.
        static_assert(
            monad_vm_req.min_required <= 2 && monad_vm_req.max_growth == 0);
        uint8_t const *new_ip;
        if (MONAD_LIKELY(charge_gas(gas_remaining, monad_vm_req.gas))) {
            new_ip = jump_impl(ctx, MONAD_VM_CODE_VIEW, *(stack_top - 1)) + 1;
        }
        else {
            gas_remaining += monad_vm_req.gas;
            MONAD_VM_CHECK(JUMP);
            new_ip = swallow_jumpdest(
                ctx,
                jump_impl(ctx, MONAD_VM_CODE_VIEW, *(stack_top - 1)),
                gas_remaining);
        }
        *(stack_top - 1) = *stack_top;
        --stack_top;
        MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*new_ip](
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
            stack_top,
            gas_remaining,
            new_ip MONAD_VM_TBL_ARG);
    }

    // SWAP1 then DUP2 or SWAP2, SWAP1's test and gas made: a b -> b a b in
    // two copies where the two opcodes make four, x y z -> y z x in two where
    // they make six. For DUP2 the pair a b moves up one slot in one
    // overlapping copy, its destination above its source, which ZisK's DMA
    // reads whole before it writes, as ziskos's memmove relies on; the new
    // top is then copied to the slot under it, and the slot above is the
    // push DUP2's test allows. For SWAP2 the deepest word is copied to the
    // slot above the top, then the words over it move down one slot in one
    // overlapping copy, its destination below its source; that slot may be
    // the one above the 1024th, which the stack keeps for it (allocator.hpp).
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swap1_then(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        if constexpr (OP == DUP2) {
            // DUP2 takes the two words SWAP1 tested: its gas, which it does
            // not test (should_check_gas), and the room for its push are left.
            static_assert(!should_check_gas(
                DUP2, compiler::opcode_table<traits>[DUP2].dynamic_gas));
            gas_remaining -= static_gas<traits, DUP2>();
            if (MONAD_UNLIKELY(stack_top.next_slot() >= MONAD_VM_STACK_LIMIT)) {
                MONAD_VM_MUST_TAIL return exit_stack_overflow(ctx);
            }
            std::memmove(&stack_top[0], &stack_top[-1], 2 * sizeof(uint256_t));
            stack_top[-1] = stack_top[1];
            stack_top += 1;
        }
        else {
            static_assert(OP == SWAP2);
            MONAD_VM_CHECK(SWAP2);
            stack_top[1] = stack_top[-2];
            std::memmove(&stack_top[-2], &stack_top[-1], 3 * sizeof(uint256_t));
        }
        MONAD_VM_DISPATCH(1, 0, *instr_ptr);
    }

    // SWAPn then SWAPm, SWAPn's tests and gas made, the word the top swaps
    // with at SRC: the top's word goes to SRC, SRC's to the m-th below the
    // top and that one's to the top, four copies where the two opcodes make
    // six. When m is n they leave the stack as it was, as the two opcodes do.
    // SWAP1 and SWAP2 swap words SWAPn has tested, n being 2 or more.
    //
    // SWAPn then ADD, SUB, AND or MSTORE: SRC's word, the top's after the
    // swap, is read where it lies, with the word under the top, and the top's
    // word goes to SRC, one copy where SWAPn makes three. SRC is two words or
    // more below the top, never the one under it, and SWAPn's test covers
    // the follower's two words. A store that grows the memory makes the swap
    // whole and takes MSTORE's growth path.
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void swapn_then(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint256_t *const src)
    {
        if constexpr (OP >= SWAP1 && OP <= SWAP4) {
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
        else if constexpr (OP == MSTORE) {
            gas_remaining -= static_gas<traits, MSTORE>();
            // Tested as mstore tests its offset, SRC's word.
            uint256_t const &monad_vm_x = *src;
            if (MONAD_UNLIKELY(
                    (monad_vm_x[1] | monad_vm_x[2] | monad_vm_x[3]) != 0)) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
            if (MONAD_UNLIKELY(monad_vm_x[0] >= ctx.memory_access32_end)) {
                bool const monad_vm_slow =
                    (monad_vm_x[0] >> runtime::Memory::offset_bits) != 0;
                // The stack as SWAPn leaves it, for MSTORE's growth path.
                uint256_t *const monad_t = &ctx.swap_scratch;
                *monad_t = *src;
                *src = *stack_top;
                *stack_top = *monad_t;
                if (MONAD_UNLIKELY(monad_vm_slow)) {
                    MONAD_VM_MUST_TAIL return mstore_slow<quiet_traits<traits>>(
                        ctx,
                        MONAD_VM_DISPATCH_STATE_ARG,
                        stack_lower_bound,
                        stack_top,
                        gas_remaining,
                        MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
                }
                MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            auto const offset = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(monad_vm_x[0]));
            runtime::mstore_at<base_traits<traits>>(
                &ctx, offset, &stack_top[-1]);
            *src = *stack_top;
            MONAD_VM_DISPATCH(1, -2, *instr_ptr);
        }
        else {
            gas_remaining -=
                static_gas<traits, static_cast<compiler::EvmOpCode>(OP)>();
            if constexpr (OP == ADD) {
                ctx.add256_params.a = reinterpret_cast<uint64_t const *>(src);
                zisk_add256(
                    ctx.add256_params, *(stack_top - 1), *(stack_top - 1));
            }
            else if constexpr (OP == SUB) {
                // As SUB: SRC's word, the swapped top, less the one under it.
                zisk_sub256_into(
                    ctx,
                    reinterpret_cast<uint64_t const *>(src),
                    *(stack_top - 1));
            }
            else {
                static_assert(OP == AND);
                *(stack_top - 1) = *src & *(stack_top - 1);
            }
            *src = *stack_top;
            MONAD_VM_DISPATCH(1, -1, *instr_ptr);
        }
    }

    // bool_push2 without a JUMPI after the push: the result written, then
    // PUSH2. Out of line, so that bool_push2 keeps its arguments where its
    // own dispatch wants them instead of copies for this arm.
    template <Traits traits>
    [[gnu::noinline]] void bool_push2_write(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint64_t const bit)
    {
        *stack_top = uint256_t{bit};
        MONAD_VM_MUST_TAIL return push<2, traits>(
            ctx,
            MONAD_VM_DISPATCH_STATE_ARG,
            stack_lower_bound,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint64_t const bit)
    {
        if (MONAD_UNLIKELY(*(instr_ptr + 3) != static_cast<uint8_t>(JUMPI))) {
            MONAD_VM_MUST_TAIL return bool_push2_write<traits>(
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
                stack_top,
                gas_remaining,
                instr_ptr MONAD_VM_TBL_ARG,
                bit);
        }
        if (MONAD_UNLIKELY(stack_top.next_slot() >= MONAD_VM_STACK_LIMIT)) {
            // An exit of its own: merged with the jump's equal one below,
            // the exit block took a copy of ctx on every execution.
            MONAD_VM_MUST_TAIL return exit_stack_overflow(ctx);
        }
        gas_remaining -= static_gas<traits, PUSH2, JUMPI>();
        MONAD_VM_LAUNDER(gas_remaining);
        if (bit) {
            // Decoded on this arm only: the other one never reads it.
            auto const monad_vm_dst =
                static_cast<size_t>(detail::load_be_k<2>(instr_ptr + 1));
            if (MONAD_UNLIKELY(
                    !MONAD_VM_CODE_VIEW.is_jumpdest16(monad_vm_dst))) {
                // A tail call: a call would keep a frame for ra.
                MONAD_VM_MUST_TAIL return ctx.exit(Error);
            }
            auto const *monad_vm_ip = MONAD_VM_CODE_VIEW.code() + monad_vm_dst;
            monad_vm_ip = swallow_jumpdest(ctx, monad_vm_ip, gas_remaining);
            instr_ptr = monad_vm_ip;
            MONAD_VM_MUST_TAIL return MONAD_VM_TABLE_REF[*instr_ptr](
                ctx,
                MONAD_VM_DISPATCH_STATE_ARG,
                stack_lower_bound,
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint64_t const bit)
    {
        MONAD_VM_CHECK(OR);
        (*(stack_top - 1))[0] |= bit;
        MONAD_VM_DISPATCH(1, -1, *instr_ptr);
    }

    // DUPn then ADD, SUB, AND, LT, GT, EQ, ISZERO, CALLDATALOAD, MLOAD,
    // MSTORE or SWAP1, DUPn's tests and gas made: the word DUPn copies, at
    // SRC, is read where it lies instead of copied to the top. A load or a
    // store that grows the memory makes the copy and takes its opcode's
    // growth path; LT's, GT's, EQ's and ISZERO's result goes to the
    // follower's head in a7, as LT's does, so that PUSH2 JUMPI branches on it
    // unwritten (bool_push2).
    template <uint8_t OP, Traits traits>
    MONAD_VM_INSTRUCTION_CALL void dup_then(
        runtime::Context &entry_ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM,
        uint256_t const *const src)
    {
        runtime::Context &ctx = held_in_a0(entry_ctx);
        if constexpr (OP == MSTORE) {
            // DUPn tested two words or more, MSTORE's two counting the copy:
            // its gas is left, which it does not test (should_check_gas).
            static_assert(!should_check_gas(
                MSTORE, compiler::opcode_table<traits>[MSTORE].dynamic_gas));
            gas_remaining -= static_gas<traits, MSTORE>();
            // Tested as mstore tests its offset.
            uint256_t const &monad_vm_x = *src;
            if (MONAD_UNLIKELY(
                    (monad_vm_x[1] | monad_vm_x[2] | monad_vm_x[3]) != 0)) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
            if (MONAD_UNLIKELY(monad_vm_x[0] >= ctx.memory_access32_end)) {
                *(stack_top + 1) = *src;
                MONAD_VM_MUST_TAIL return mstore_grow<traits>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top + 1,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            auto const offset = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(monad_vm_x[0]));
            runtime::mstore_at<base_traits<traits>>(&ctx, offset, &*stack_top);
            MONAD_VM_DISPATCH(1, -1, *instr_ptr);
        }
        else if constexpr (OP == MLOAD) {
            // MLOAD's word is DUPn's copy, whose room DUPn tested: its gas is
            // left, which it does not test (should_check_gas).
            static_assert(!should_check_gas(
                MLOAD, compiler::opcode_table<traits>[MLOAD].dynamic_gas));
            gas_remaining -= static_gas<traits, MLOAD>();
            // Tested as mload tests its offset.
            uint256_t const &monad_vm_x = *src;
            if (MONAD_UNLIKELY(
                    (monad_vm_x[1] | monad_vm_x[2] | monad_vm_x[3]) != 0)) {
                MONAD_VM_MUST_TAIL return ctx.exit(OutOfGas);
            }
            auto const offset = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(monad_vm_x[0]));
            if (MONAD_UNLIKELY(monad_vm_x[0] >= ctx.memory_access32_end)) {
                *(stack_top + 1) = *src;
                MONAD_VM_MUST_TAIL return mload_grow<quiet_traits<traits>>(
                    ctx,
                    MONAD_VM_DISPATCH_STATE_ARG,
                    stack_lower_bound,
                    stack_top + 1,
                    gas_remaining,
                    MONAD_VM_AS_CALLED(instr_ptr) MONAD_VM_TBL_ARG);
            }
            runtime::mload_at<base_traits<traits>>(&ctx, &stack_top[1], offset);
            MONAD_VM_DISPATCH(1, 1, *instr_ptr);
        }
        else if constexpr (OP == SWAP1) {
            // The old top one slot up, the copied word under it.
            gas_remaining -= static_gas<traits, SWAP1>();
            *(stack_top + 1) = *stack_top;
            *stack_top = *src;
            MONAD_VM_DISPATCH(1, 1, *instr_ptr);
        }
        else if constexpr (OP == CALLDATALOAD) {
            // The offset read where it lies, the word loaded to the top.
            gas_remaining -= static_gas<traits, CALLDATALOAD>();
            runtime::calldataload(&ctx, &stack_top[1], src);
            MONAD_VM_DISPATCH(1, 1, *instr_ptr);
        }
        else if constexpr (OP == ISZERO || OP == EQ) {
            // ISZERO's result takes the copy's slot, EQ's the top's.
            constexpr std::ptrdiff_t monad_vm_at = OP == ISZERO ? 1 : 0;
            bool const monad_vm_bit =
                OP == ISZERO
                    ? !*src
                    : zisk_equal32(
                          reinterpret_cast<uint64_t const *>(src),
                          reinterpret_cast<uint64_t const *>(&*(stack_top)));
            gas_remaining -=
                static_gas<traits, static_cast<compiler::EvmOpCode>(OP)>();
            MONAD_VM_LEAD_DISPATCH_BIT(
                bool_offset(lag_of<traits>),
                *(instr_ptr + 1),
                stack_top + monad_vm_at,
                gas_remaining,
                instr_ptr - lag_of<traits>,
                static_cast<uint64_t>(monad_vm_bit));
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
                zisk_sub256_into(
                    ctx, reinterpret_cast<uint64_t const *>(src), *stack_top);
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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CREATE, runtime::create<base_traits<traits>>);

        MONAD_VM_NEXT(CREATE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(CALL, runtime::call<base_traits<traits>>);

        MONAD_VM_NEXT(CALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CALLCODE, runtime::callcode<base_traits<traits>>);

        MONAD_VM_NEXT(CALLCODE);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            DELEGATECALL, runtime::delegatecall<base_traits<traits>>);

        MONAD_VM_NEXT(DELEGATECALL);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            CREATE2, runtime::create2<base_traits<traits>>);

        MONAD_VM_NEXT(CREATE2);
    }

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
        uint256_t const *stack_lower_bound, StackTop stack_top,
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        MONAD_VM_CHECKED_RUNTIME_CALL(
            STATICCALL, runtime::staticcall<base_traits<traits>>);

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
        runtime::Context &ctx, MONAD_VM_DISPATCH_STATE_PARAM,
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
        int64_t gas_remaining, uint8_t const *instr_ptr MONAD_VM_TBL_PARAM)
    {
        fuzz_tstore_stack(
            ctx, stack_lower_bound, stack_top, MONAD_VM_CODE_VIEW.size());
        MONAD_VM_CHECKED_RUNTIME_CALL(
            SELFDESTRUCT, runtime::selfdestruct<base_traits<traits>>);
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
