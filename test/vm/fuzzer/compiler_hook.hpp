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

#include <category/vm/compiler/ir/x86/emitter.hpp>
#include <category/vm/compiler/ir/x86/virtual_stack.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>

#include <array>
#include <cstdint>
#include <random>

namespace monad::vm::fuzzing
{
    /**
     * The fuzzer has a hard time exploring edge case virtual stack
     * states. To circumvent this we will artificially change the state
     * of the stack to increase probability of having stack elements in
     * different locations.
     */
    template <typename Engine>
    auto compiler_emit_hook(Engine &engine)
    {
        static constexpr std::array<double, 2> artificial_swap_probs = {
            0, 0.50};
        double const artificial_swap_prob =
            uniform_sample(engine, artificial_swap_probs);

        static constexpr std::array<double, 2> artificial_peak_probs = {
            0, 0.75};
        double const artificial_peak_prob =
            uniform_sample(engine, artificial_peak_probs);

        static constexpr std::array<double, 3> artificial_avx_probs = {
            0, 0.5, 1.0};
        double const artificial_avx_prob =
            uniform_sample(engine, artificial_avx_probs);

        static constexpr std::array<double, 3> artificial_general_probs = {
            0, 0.5, 1.0};
        double const artificial_general_prob =
            uniform_sample(engine, artificial_general_probs);

        double const artificial_top2_prob =
            std::min(1.0, artificial_avx_prob + artificial_general_prob);

        return [artificial_swap_prob,
                artificial_peak_prob,
                artificial_avx_prob,
                artificial_general_prob,
                artificial_top2_prob,
                &engine](
                   vm::compiler::native::Emitter &emit,
                   auto block_id,
                   auto instr_ix,
                   auto instr) {
            (void)block_id;
            (void)instr_ix;
            (void)instr; // Unused
            using monad::vm::compiler::native::GENERAL_REG_COUNT;
            using monad::vm::compiler::native::GeneralReg;

            auto &stack = emit.get_stack();
            if (stack.top_index() < stack.min_delta()) {
                // Do nothing when the stack is empty.
                return;
            }

            emit.checked_debug_comment("BEGIN artificial setup");

            // For each general reg, potentially exchange two gpq registers.
            std::uniform_int_distribution<uint8_t> general_reg_index_dist{0, 3};
            for (uint8_t i = 0; i < compiler::native::GENERAL_REG_COUNT; ++i) {
                with_probability(engine, artificial_swap_prob, [&](auto &) {
                    emit.swap_general_reg_indices(
                        compiler::native::GeneralReg{i},
                        general_reg_index_dist(engine),
                        general_reg_index_dist(engine));
                });
            }

            auto mov_to_stack_offset = [&](std::int32_t i) -> bool {
                if (stack.has_deferred_comparison_at(i)) {
                    return false;
                }
                if (stack.get(i)->stack_offset()) {
                    return true;
                }
                emit.mov_stack_index_to_stack_offset(i);
                return true;
            };

            auto mov_to_avx_reg = [&](std::int32_t i) -> bool {
                if (stack.has_deferred_comparison_at(i)) {
                    return false;
                }
                if (stack.get(i)->avx_reg()) {
                    return true;
                }
                emit.mov_stack_index_to_avx_reg(i);
                return true;
            };

            auto mov_to_general_reg = [&](std::int32_t i) -> bool {
                if (stack.has_deferred_comparison_at(i)) {
                    return false;
                }
                if (stack.get(i)->general_reg()) {
                    return true;
                }
                emit.mov_stack_index_to_general_reg(i);
                return true;
            };

            auto mov_to_locations = [&](std::int32_t i,
                                        bool lit,
                                        bool gen,
                                        bool avx,
                                        bool sta) -> bool {
                if (stack.has_deferred_comparison_at(i)) {
                    return false;
                }

                auto e = stack.get(i);

                // Make sure at least one location is present:
                if (e->literal() && (lit | gen | avx | sta) == false) {
                    auto dist = std::uniform_int_distribution<int>{0, 3};
                    switch (dist(engine)) {
                    case 0:
                        lit = true;
                        break;
                    case 1:
                        gen = true;
                        break;
                    case 2:
                        avx = true;
                        break;
                    case 3:
                        sta = true;
                        break;
                    }
                }
                else if ((gen | avx | sta) == false) {
                    auto dist = std::uniform_int_distribution<int>{1, 3};
                    switch (dist(engine)) {
                    case 1:
                        gen = true;
                        break;
                    case 2:
                        avx = true;
                        break;
                    case 3:
                        sta = true;
                        break;
                    }
                }

                if (gen) {
                    mov_to_general_reg(i);
                }
                if (avx) {
                    mov_to_avx_reg(i);
                }
                if (sta) {
                    mov_to_stack_offset(i);
                }
                if (!lit && e->literal()) {
                    stack.spill_literal(e);
                }
                if (!gen && e->general_reg()) {
                    auto *s = stack.spill_general_reg(e);
                    MONAD_VM_ASSERT(s == nullptr);
                }
                if (!avx && e->avx_reg()) {
                    auto *s = stack.spill_avx_reg(e);
                    MONAD_VM_ASSERT(s == nullptr);
                }
                if (!sta && e->stack_offset()) {
                    stack.spill_stack_offset(e);
                }
                return true;
            };

            // At stack peak, we will spill everything to memory with
            // some probability to test that we do not run out of stack
            // offsets during the next instruction.
            if (stack.top_index() == stack.max_delta() - 1) {
                with_probability(engine, artificial_peak_prob, [&](auto &) {
                    auto e = stack.max_delta();
                    for (auto i = stack.min_delta(); i < e; ++i) {
                        mov_to_stack_offset(i);
                    }
                });
            }

            with_probability(engine, artificial_avx_prob, [&](auto &) {
                // Try to write 13 to 16 stack elems to avx reg location.
                auto ndist =
                    std::uniform_int_distribution<std::int32_t>{13, 16};
                auto const n = ndist(engine);
                auto offdist =
                    std::uniform_int_distribution<std::int32_t>{2, 5};
                auto off = offdist(engine);
                auto const d = stack.min_delta();
                std::int32_t count = 0;
                for (auto i = stack.top_index() - off; i >= d; --i) {
                    count += mov_to_avx_reg(i);
                    if (count == n) {
                        break;
                    }
                }
            });

            with_probability(engine, artificial_general_prob, [&](auto &) {
                // Try to write -3 to 3 stack elems to general reg location,
                // negative meaning spill (remove general reg locations).
                auto ndist = std::uniform_int_distribution<std::int32_t>{-3, 3};
                auto const n = ndist(engine);

                if (n == 0) {
                    return;
                }

                if (n > 0) {
                    auto offdist =
                        std::uniform_int_distribution<std::int32_t>{2, 5};
                    auto off = offdist(engine);
                    auto const d = stack.min_delta();
                    std::int32_t count = 0;
                    for (auto i = stack.top_index() - off; i >= d; --i) {
                        count += mov_to_general_reg(i);
                        if (count == n) {
                            break;
                        }
                    }
                    return;
                }

                auto gdist = std::uniform_int_distribution<std::uint8_t>{
                    0, GENERAL_REG_COUNT - 1};
                std::uint8_t g = gdist(engine);
                size_t count = 0;
                for (auto i = n; i < 0 && count < GENERAL_REG_COUNT; ++count) {
                    auto *e = stack.general_reg_stack_elem(GeneralReg{g});
                    g = uint8_t((g + 1) % GENERAL_REG_COUNT);

                    if (!e) {
                        continue;
                    }

                    auto const &ixs = e->stack_indices();
                    MONAD_VM_ASSERT(!ixs.empty());
                    auto ix = *ixs.begin();
                    if (!e->literal() && !e->stack_offset() && !e->avx_reg()) {
                        emit.mov_stack_index_to_stack_offset(ix);
                    }
                    auto *s = stack.spill_general_reg(e);
                    MONAD_VM_ASSERT(s == nullptr);
                }
            });

            with_probability(engine, artificial_top2_prob, [&](auto &) {
                // Try to put the top 2 stack elements in specific locations.

                auto i = std::max(stack.top_index() - 1, stack.min_delta());
                auto e = stack.top_index() + 1;
                auto dist = std::uniform_int_distribution<int>{0, 1};
                for (; i < e; ++i) {
                    bool const lit = dist(engine) == 1;
                    bool const gen = dist(engine) == 1;
                    bool const avx = dist(engine) == 1;
                    bool const sta = dist(engine) == 1;
                    mov_to_locations(i, lit, gen, avx, sta);
                }

                // Swap general registers to increase variance of
                // general register locations.
                auto *x0 = stack.general_reg_stack_elem(GeneralReg{0});
                auto *x1 = stack.general_reg_stack_elem(GeneralReg{1});
                auto *x2 = stack.general_reg_stack_elem(GeneralReg{2});
                if (x0 && x1 && x2) {
                    if (dist(engine) == 0) {
                        emit.swap_general_regs(*x0, *x1);
                    }
                    else {
                        emit.swap_general_regs(*x1, *x2);
                    }
                }
                else if (x0 && x1) {
                    emit.swap_general_regs(*x0, *x1);
                }
                else if (x1 && x2) {
                    emit.swap_general_regs(*x1, *x2);
                }
                else if (x0 && x2) {
                    emit.swap_general_regs(*x0, *x2);
                }
            });

            emit.checked_debug_comment("END artificial setup");
        };
    }

}
