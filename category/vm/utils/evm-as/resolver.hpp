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

#include <category/vm/core/cases.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/utils.hpp>

#include <evmc/evmc.h>

#include <map>

namespace monad::vm::utils::evm_as
{
    template <Traits traits>
    std::unordered_map<std::string, size_t>
    resolve_labels(EvmBuilder<traits> const &eb)
    {
        std::unordered_map<std::string, size_t> label_offsets{};

        // First pass: initialize the data structures
        size_t offset = 0;
        for (Instruction::T const &ins : eb) {
            if (Instruction::is_comment(ins)) {
                continue;
            }

            offset =
                offset +
                std::visit(
                    Cases{
                        [&](PushLabelI const &) -> size_t {
                            return 1; // optimistically assume a 1 byte
                                      // encoding.
                        },
                        [&label_offsets,
                         offset](JumpdestI const &jumpdest) -> size_t {
                            auto const [it, _] =
                                label_offsets.insert({jumpdest.label, offset});
                            MONAD_VM_ASSERT(it != label_offsets.end());
                            return 1; // 1 byte encoding.
                        },
                        [](PushI const &push) -> size_t {
                            return 1 + push.n(); // 1 + N byte encoding.
                        },
                        [](PlainI const &) -> size_t {
                            return 1; // 1 byte encoding
                        },
                        [](InvalidI const &) -> size_t { return 1; },
                        [](auto const &) -> size_t { MONAD_VM_ASSERT(false); }},
                    ins);
        }

        // Second pass: keep refining label offset estimates until
        // a fixed point has been reached.
        bool stable = false;
        while (!stable) {
            stable = true;
            size_t prev_offset = 0;
            offset = 0;
            for (Instruction::T const &ins : eb) {
                if (Instruction::is_comment(ins)) {
                    continue;
                }

                offset =
                    offset +
                    std::visit(
                        Cases{
                            [&](PushLabelI const &push) -> size_t {
                                auto const it = label_offsets.find(push.label);
                                if (it == label_offsets.end()) {
                                    // Push of undefined label compiles to
                                    // a single byte invalid instruction,
                                    // so increase offset by one.
                                    return 1;
                                }
                                auto const offset = it->second;
                                size_t const n =
                                    offset == 0 ? 0 : byte_width(offset);

                                // Expand to either PUSH0 or
                                // PUSHn.
                                return 1 + n;
                            },
                            [offset, &label_offsets, &stable](
                                JumpdestI const &jumpdest) -> size_t {
                                auto const it =
                                    label_offsets.find(jumpdest.label);
                                MONAD_VM_ASSERT(it != label_offsets.end());

                                // Check whether our estimated position of
                                // this jumpdest has changed, if so update
                                // it.
                                if (it->second != offset) {
                                    stable = false;
                                    it->second = offset;
                                }
                                return 1;
                            },
                            [](PushI const &push) -> size_t {
                                return 1 + push.n(); // 1 + N byte encoding.
                            },
                            [](PlainI const &) -> size_t {
                                return 1; // 1 byte encoding
                            },
                            [](InvalidI const &) -> size_t { return 1; },
                            [](auto const &) -> size_t {
                                MONAD_VM_ASSERT(false);
                            }},
                        ins);

                // Overflow check. If the below assertion triggers,
                // then it means that the program size exceeds
                // the maximum (implementation-defined)
                // limit. However, it should never be possible to
                // reach this point, because the builder object
                // would have to allocate more than the
                // `std::numeric_limits<size_t>::max()` amount of
                // instructions, which ought to have triggered an
                // out of memory error by now.
                MONAD_VM_ASSERT(offset >= prev_offset);
                prev_offset = offset;
            }
        }
        return label_offsets;
    }
}
