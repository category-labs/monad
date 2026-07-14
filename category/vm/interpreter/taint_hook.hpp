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

// Slot-taint experiment: post-instruction tag maintenance for the shadow
// stack (see category/vm/runtime/taint.hpp). Runs from the MONAD_VM_NEXT
// dispatch macros with the pre-delta stack_top, i.e. after the instruction
// body executed but before the stack pointer advances, so consumed operand
// residue above the new top is still readable.

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/runtime/taint.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstdint>

namespace monad::vm::interpreter
{
    inline uint32_t &taint_tag(
        runtime::TaintFrame &frame, uint256_t const *stack_bottom,
        uint256_t const *cell)
    {
        return frame.tags[static_cast<size_t>(cell - (stack_bottom + 1))];
    }

    // Pre-body hook for comparison instructions: records constraints on
    // tainted operands (instead of revoking) and clears their tags, so the
    // generic post-instruction arm sees only untainted cells. Runs after
    // check_requirements, so operand cells are valid.
    template <uint8_t Op>
    void taint_before_compare(
        runtime::Context &ctx, uint256_t const *stack_bottom,
        uint256_t *stack_top) noexcept
    {
        auto &frame = *static_cast<runtime::TaintFrame *>(ctx.taint_frame);
        if (frame.live == 0) {
            return;
        }
        constexpr bool unary = Op == 0x15; // ISZERO
        uint32_t &tl = taint_tag(frame, stack_bottom, stack_top);
        uint32_t zero_tag = 0;
        uint32_t &tr =
            unary ? zero_tag : taint_tag(frame, stack_bottom, stack_top - 1);
        if (tl == 0 && tr == 0) {
            return;
        }
        uint256_t const &lhs = *stack_top;
        uint256_t const rhs = unary ? uint256_t{0} : *(stack_top - 1);
        frame.registry->record_compare(Op, tl, lhs, tr, rhs);
        frame.live -= (tl != 0);
        frame.live -= (tr != 0);
        tl = 0;
        tr = 0;
    }

    // Pre-body hook for AND: an identity mask (observed value unchanged)
    // records a MASK_PASS constraint and lets the taint flow through to the
    // result cell; a genuine extraction pins the result as a constant via
    // MASK_EXTRACT. Both re-checked at merge.
    inline void taint_before_and(
        runtime::Context &ctx, uint256_t const *stack_bottom,
        uint256_t *stack_top) noexcept
    {
        auto &frame = *static_cast<runtime::TaintFrame *>(ctx.taint_frame);
        if (frame.live == 0) {
            return;
        }
        uint32_t &ta = taint_tag(frame, stack_bottom, stack_top);
        uint32_t &tb = taint_tag(frame, stack_bottom, stack_top - 1);
        if (ta == 0 && tb == 0) {
            return;
        }
        if (ta != 0 && tb != 0) {
            frame.registry->revoke(ta);
            frame.registry->revoke(tb);
            frame.live -= 2;
            ta = 0;
            tb = 0;
            return;
        }
        uint32_t &tv = ta != 0 ? ta : tb;
        uint256_t const &tainted_val = ta != 0 ? *stack_top : *(stack_top - 1);
        uint256_t const &mask = ta != 0 ? *(stack_top - 1) : *stack_top;
        uint256_t const r = tainted_val & mask;
        if (r == tainted_val) {
            frame.registry->record_value_constraint(
                tv, runtime::TAINT_MASK_PASS, mask, uint256_t{0});
            // taint survives on the result cell (body writes to top - 1);
            // net live count is unchanged: one tag cleared, one written
            uint32_t const keep = tv;
            ta = 0;
            tb = 0;
            taint_tag(frame, stack_bottom, stack_top - 1) = keep;
        }
        else {
            frame.registry->record_value_constraint(
                tv, runtime::TAINT_MASK_EXTRACT, mask, r);
            frame.live -= 1;
            ta = 0;
            tb = 0;
        }
    }

    // Pre-body hook for SHR: pins the shifted result as a constant.
    inline void taint_before_shr(
        runtime::Context &ctx, uint256_t const *stack_bottom,
        uint256_t *stack_top) noexcept
    {
        auto &frame = *static_cast<runtime::TaintFrame *>(ctx.taint_frame);
        if (frame.live == 0) {
            return;
        }
        uint32_t &tshift = taint_tag(frame, stack_bottom, stack_top);
        uint32_t &tval = taint_tag(frame, stack_bottom, stack_top - 1);
        if (tshift != 0) {
            frame.registry->revoke(tshift);
            frame.live -= 1;
            tshift = 0;
        }
        if (tval == 0) {
            return;
        }
        uint256_t const &shift = *stack_top;
        uint256_t const &value = *(stack_top - 1);
        uint256_t const r = shift < 256 ? value >> shift : uint256_t{0};
        frame.registry->record_value_constraint(
            tval, runtime::TAINT_SHR_EXTRACT, shift, r);
        frame.live -= 1;
        tval = 0;
    }

    template <uint8_t Op, Traits traits>
    void taint_after_instruction(
        runtime::Context &ctx, uint256_t const *stack_bottom,
        uint256_t *stack_top) noexcept
    {
        using namespace monad::vm::compiler;

        auto &frame = *static_cast<runtime::TaintFrame *>(ctx.taint_frame);
        // Fast path: nothing is live and this op cannot create taint, so
        // every tag it could touch is already 0.
        if constexpr (Op != SLOAD) {
            if (frame.live == 0) {
                return;
            }
        }
        auto *reg = frame.registry;
        auto const tag = [&](uint256_t const *cell) -> uint32_t & {
            return taint_tag(frame, stack_bottom, cell);
        };

        if constexpr (Op == ADD || Op == SUB) {
            // body computed the result into *(stack_top - 1); operand `a`
            // survives at *stack_top
            uint32_t const ta = tag(stack_top);
            uint32_t const tb = tag(stack_top - 1);
            uint32_t result_tag = 0;
            if (ta != 0 && tb != 0) {
                reg->revoke(ta);
                reg->revoke(tb);
            }
            else if (ta != 0) {
                // a tainted: result = a OP b with untainted b
                uint256_t const a = *stack_top;
                uint256_t const r = *(stack_top - 1);
                uint256_t const b = Op == ADD ? r - a : a - r;
                uint256_t const off =
                    Op == ADD ? reg->offset_of(ta) + b : reg->offset_of(ta) - b;
                result_tag = reg->derive(ta, off);
            }
            else if (tb != 0) {
                if constexpr (Op == ADD) {
                    // b tainted: result = a + (v + c) -> offset c + a
                    result_tag =
                        reg->derive(tb, reg->offset_of(tb) + *stack_top);
                }
                else {
                    // a - tainted: negatively proportional -> revoke
                    reg->revoke(tb);
                }
            }
            frame.live += (result_tag != 0);
            frame.live -= (ta != 0);
            frame.live -= (tb != 0);
            tag(stack_top) = 0;
            tag(stack_top - 1) = result_tag;
        }
        else if constexpr (Op == AND || Op == SHR) {
            // pre-body hooks arranged the tags; consumed operand cell above
            // the result is retired
            uint32_t &t = tag(stack_top);
            frame.live -= (t != 0);
            t = 0;
        }
        else if constexpr (Op == POP) {
            // discarding a tainted value is not a leak
            uint32_t &t = tag(stack_top);
            frame.live -= (t != 0);
            t = 0;
        }
        else if constexpr (Op >= DUP1 && Op <= DUP16) {
            constexpr auto n = Op - DUP1 + 1;
            uint32_t const src = tag(stack_top - (n - 1));
            uint32_t &dst = tag(stack_top + 1);
            frame.live += (src != 0);
            frame.live -= (dst != 0);
            dst = src;
        }
        else if constexpr (Op >= SWAP1 && Op <= SWAP16) {
            // pure permutation: live count unchanged
            constexpr auto n = Op - SWAP1 + 1;
            uint32_t const t = tag(stack_top);
            tag(stack_top) = tag(stack_top - n);
            tag(stack_top - n) = t;
        }
        else if constexpr (Op == SLOAD) {
            // wrapper registered the load pre-body; result replaced the key
            uint32_t &t = tag(stack_top);
            frame.live += (frame.pending_load != 0);
            frame.live -= (t != 0);
            t = frame.pending_load;
            frame.pending_load = 0;
        }
        else if constexpr (Op == SSTORE) {
            // wrapper registered the store pre-body; consumed cells retire
            uint32_t &ka = tag(stack_top);
            uint32_t &kb = tag(stack_top - 1);
            frame.live -= (ka != 0);
            frame.live -= (kb != 0);
            ka = 0;
            kb = 0;
        }
        else {
            // generic rule: any other consumption of a tainted value revokes
            // its origin slot; all outputs are untainted
            constexpr auto info = compiler::opcode_table<traits>[Op];
            constexpr auto inputs = info.min_stack;
            constexpr auto delta = static_cast<int32_t>(info.stack_increase) -
                                   static_cast<int32_t>(info.min_stack);
            constexpr auto outputs =
                static_cast<int32_t>(info.min_stack) + delta;
            for (uint32_t i = 0; i < inputs; ++i) {
                uint32_t &t = tag(stack_top - i);
                if (t != 0) {
                    reg->revoke(t);
                    frame.live -= 1;
                    t = 0;
                }
            }
            uint256_t *const new_top = stack_top + delta;
            for (int32_t i = 0; i < outputs; ++i) {
                uint32_t &t = tag(new_top - i);
                frame.live -= (t != 0);
                t = 0;
            }
        }
    }
}
