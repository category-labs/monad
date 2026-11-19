// Copyright (C) 2025-26 Category Labs, Inc.
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

#if !defined(MONAD_ZKVM_ZISK)
    #include_next <category/vm/interpreter/intrinsics.hpp>
#else
    #include <cstddef>
    #include <cstdint>
    #include <utility>

// bext extracts bit I % 64 in one instruction. Use asm because GCC misses this
// pattern with a masked shift count. Removing the mask in C++ would make shifts
// by 64 or more undefined.
    #define MONAD_VM_TEST_BIT(WORD, I)                                         \
        ({                                                                     \
            uint64_t const monad_vm_word = (WORD);                             \
            uint64_t monad_vm_bit;                                             \
            asm(".option push\n\t"                                             \
                ".option arch, +zbs\n\t"                                       \
                "bext %0, %1, %2\n\t"                                          \
                ".option pop"                                                  \
                : "=r"(monad_vm_bit)                                           \
                : "r"(monad_vm_word), "r"(I));                                 \
            monad_vm_bit != 0;                                                 \
        })

namespace monad::vm::interpreter
{
    namespace detail
    {
        // Assemble K big-endian bytes directly to avoid a temporary and a
        // software byte swap on targets without a byte-swap instruction.
        template <size_t K>
        [[gnu::always_inline]] inline uint64_t
        load_be_k(uint8_t const *const p) noexcept
        {
            static_assert(K >= 1 && K <= 8);
            // ZisK charges less for two byte loads + packh than lhu/rev8/srli.
            // Memory operands let GCC fold pointer offsets into the loads.
            if constexpr (K == 2) {
                uint64_t hi;
                uint64_t lo;
                // %0 = hi, %1 = lo; %2/%3 address p[0]/p[1].
                // "=&r": write-only registers, distinct from input addresses.
                // lbu zero-extends each byte.
                asm("lbu %0, %2\n\t" // hi = p[0]
                    "lbu %1, %3\n\t" // lo = p[1]
                    "packh %0, %1, %0" // hi = (hi << 8) | lo
                    : "=&r"(hi), "=&r"(lo)
                    : "m"(p[0]), "m"(p[1]));
                return hi;
            }
            // Use lwu instead of lw to avoid ZisK's sign-extension cost.
            // rev8 and srli convert the four bytes from big-endian.
            if constexpr (K == 4) {
                uint64_t v;
                asm("lwu %0, %1\n\t"
                    "rev8 %0, %0\n\t"
                    "srli %0, %0, 32"
                    : "=r"(v)
                    : "m"(*reinterpret_cast<uint8_t const(*)[4]>(p)));
                return v;
            }
            return [p]<size_t... Is>(std::index_sequence<Is...>) {
                return (
                    (static_cast<uint64_t>(p[Is]) << (8 * (K - 1 - Is))) | ...);
            }(std::make_index_sequence<K>{});
        }
    }
}
#endif
