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

// Guest EVM MUL: ZisK's precompile or the portable uint256 operator.

#pragma once

#include <category/core/runtime/uint256.hpp>

#ifdef MONAD_ZKVM_ZISK
namespace monad::vm::runtime
{
    // ZisK computes a * b + c = (dh << 256) | dl; MUL keeps dl with c = 0.
    // Restrict this path to EVM MUL: general-purpose multiplication may be
    // cheaper in software for small operands.
    struct ZiskArith256Params
    {
        uint64_t const *a;
        uint64_t const *b;
        uint64_t const *c;
        uint64_t *dl;
        uint64_t *dh;
    };
}
#endif

namespace monad::vm::runtime
{
    inline void
    mul(uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *b_ptr) noexcept
    {
#ifdef MONAD_ZKVM_ZISK
        // uint256_t matches the precompile's layout and alignment, so pass
        // operands directly without copying them.
        static_assert(alignof(uint256_t) >= 8);
        static_assert(sizeof(uint256_t) == 4 * sizeof(uint64_t));
        // Reuse the parameter block: only a, b and dl change per call.
        // The guest is single-threaded and the precompile cannot reenter mul.
        alignas(8) static constexpr uint64_t zero[4] = {0, 0, 0, 0};
        alignas(8) static uint64_t hi[4];
        // Constant initialization avoids a guard on each call.
        static ZiskArith256Params p{nullptr, nullptr, zero, nullptr, hi};
        p.a = reinterpret_cast<uint64_t const *>(a_ptr);
        p.b = reinterpret_cast<uint64_t const *>(b_ptr);
        // Inputs are read before either output is written, so result may alias
        // a or b (opc_arith256 and MemBusHelpers::mem_aligned_op).
        p.dl = reinterpret_cast<uint64_t *>(result_ptr);
        // Inline ZisK's arith256 marker (port 0x801) to avoid a wrapper call.
        asm volatile(".option push\n\t"
                     ".option arch, +zicsr\n\t"
                     "csrs 0x801, %0\n\t"
                     ".option pop"
                     :
                     : "r"(&p)
                     : "memory");
#else
        *result_ptr = *a_ptr * *b_ptr;
#endif
    }
}
