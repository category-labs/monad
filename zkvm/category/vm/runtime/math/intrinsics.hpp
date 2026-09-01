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

// zkVM fallback for the runtime math `mul`: uses the in-tree uint256
// operator overload rather than the hand-rolled x86 assembly.

#pragma once

#include <category/core/runtime/uint256.hpp>

#ifdef MONAD_ZKVM_ZISK
namespace monad::vm::runtime
{
    // ZisK's arith256 precompile computes `a * b + c = dh | dl` in one step, and
    // the EVM's MUL is exactly its low half with c = 0. The C++ operator is Comba
    // over four limbs instead: measured on block 25552051, 138,035 MULs at 82.0
    // steps each -- ten hardware multiplies at 97 cells, twenty adds and six carry
    // propagations apiece -- against the precompile's 1,440 cells and one call.
    //
    // The same door the SP1 arm already uses for MUL through sys_bigint. ZisK's was
    // reached only by div_rem256_c, for the division check, and by MULMOD through
    // arith256_mod: on that block arith256 ran 11,507 times against the MUL
    // opcode's 138,035.
    //
    // Here and not in uint256_t::operator*, which is also the multiply behind gas
    // and memory-expansion arithmetic where one operand is a small constant and the
    // software path folds away. This routes the EVM opcode and nothing else.
    struct ZiskArith256Params
    {
        uint64_t const *a;
        uint64_t const *b;
        uint64_t const *c;
        uint64_t *dl;
        uint64_t *dh;
    };

    extern "C" void syscall_arith256(ZiskArith256Params *params);
}
#endif

namespace monad::vm::runtime
{
    inline void
    mul(uint256_t *result_ptr, uint256_t const *a_ptr,
        uint256_t const *b_ptr) noexcept
    {
#ifdef MONAD_ZKVM_ZISK
        // The operands are read where they lie. A uint256_t is at least 8-aligned
        // and its words are the little-endian limb order the syscall wants, so
        // staging them into locals buys nothing and costs eight loads and twelve
        // stores a call -- 582 cells of MEMORY per MUL, which on block 25552051
        // took the precompile's gain from -0.594 % down to -0.043 %. That is the
        // cost of a rejected variant, not of the routing below: the point is that
        // the copies are what nearly cancelled it, so do not reintroduce them.
        static_assert(alignof(uint256_t) >= 8);
        static_assert(sizeof(uint256_t) == 4 * sizeof(uint64_t));
        // The params block is built once, not per call. Three of its five
        // fields never change -- the zero addend and the two result buffers --
        // and the syscall needs the block's address, so a stack-local one
        // stores all five every time. Static, they are two stores.
        //
        // Safe because this is the only writer: the guest is single-threaded
        // and nothing runs between filling the block and reading the result,
        // so no call can be in flight while another fills it. The invariant is
        // not one the compiler checks -- a reentrant mul would corrupt lo under
        // its own caller -- so nothing may call into this file between the
        // syscall and the read below.
        alignas(8) static constexpr uint64_t zero[4] = {0, 0, 0, 0};
        alignas(8) static uint64_t lo[4];
        alignas(8) static uint64_t hi[4];
        // The two nullptrs are what keep the initialiser constant, and that is
        // the point of writing a and b separately instead of in the braces.
        // Braced with a_ptr and b_ptr the initialiser depends on the arguments,
        // so the static is initialised on first use and gcc guards it: not just
        // the one-time __cxa_guard_acquire, but a guard byte loaded, an acquire
        // `fence r,rw` and a branch on EVERY entry. Checked on this compiler --
        // constant, the whole body is two `sd` and the tail call; argument-
        // dependent, the fence and test precede it. The barrier alone would
        // cost more per MUL than the three stores being saved.
        static ZiskArith256Params p{nullptr, nullptr, zero, lo, hi};
        p.a = reinterpret_cast<uint64_t const *>(a_ptr);
        p.b = reinterpret_cast<uint64_t const *>(b_ptr);
        syscall_arith256(&p);
        // Through a local and not straight into result_ptr: the interface allows
        // result to be one of the operands, and the precompile's write order is
        // not ours to assume.
        *result_ptr = uint256_t{lo[0], lo[1], lo[2], lo[3]};
#else
        *result_ptr = *a_ptr * *b_ptr;
#endif
    }
}
