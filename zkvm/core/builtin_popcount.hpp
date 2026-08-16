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

// Force-included into every guest C++ translation unit from
// zkvm/guest/CMakeLists.txt. Do not #include it by hand.
//
// riscv64ima has no `cpop`, so every __builtin_popcount{,l,ll} gcc emits
// becomes a call into libgcc's 30-instruction SWAR helper -- twelve of whose
// instructions rebuild the four masks from lui/addi/slli/add on every call.
//
// zkvm/core/libc.cpp already defines __popcountdi2 to take that call over with
// a 19-instruction body that fetches the masks instead of materialising them.
// That is worth 0.14 % of the block. Replacing the *builtin* is worth
// 0.359 % -- measured, block 25551991 -- because inlining lets gcc lift the
// mask setup out of the caller's loop, which a call can never do. immer's
// HAMT makes 41,909 of these per block, one per level of every lookup and
// every insert, and is the guest's only popcount traffic: with this header in
// place __popcountdi2 is absent from the linked image entirely.
//
// This supersedes the immer hunk that used to sit in third_party/patches/.
// The two measure byte-identically -- 117,870,371 steps, 18,812,345,445 COST
// either way -- and this one is carried by this repository rather than by a
// fork of a submodule.
//
// Redefining a builtin as a function-like macro is ordinary preprocessing:
// __builtin_popcountll is just an identifier until the `(`. The three names
// tokenise separately, so defining __builtin_popcount does *not* capture
// __builtin_popcountll; each is named explicitly.
//
// The bodies are constexpr and their mask fetches take the consteval branch of
// bits::imm64, so constant expressions still fold -- including libstdc++'s
// <bit>, which this header necessarily precedes.
//
// Quoted-relative so it resolves against this file rather than the include
// path: third-party guest targets do not all carry -I${MONAD_ROOT}.
#include "../../category/core/bit_primitives.hpp"

namespace monad::bits
{
    // Deliberately *not* bits::popcount64, though the two differ only in
    // whether the second mask is hoisted into a `const` local.
    //
    // Standalone, hoisting is a pessimisation and popcount64 is right to
    // refuse it: gcc constant-evaluates a const-initialised local through
    // `if !consteval` and rebuilds the mask with li/addi/slli/add, which is 27
    // instructions against 25.
    //
    // In the guest it is the other way round, by 0.124 % of the block. The
    // caller is immer's HAMT descent, which popcounts once per level in a
    // loop; a materialised constant is loop-invariant arithmetic that LICM
    // lifts out of that loop, and an `asm` load is not something gcc will
    // lift as readily. Four loads per call beats four rebuilt constants per
    // call, and one constant per *loop* beats both.
    //
    // Measured, not reasoned -- same build, same block, only this body
    // changed: 18,837,288,704 COST with popcount64 here, 18,812,345,445 with
    // this. Do not "simplify" this to popcount64 without re-measuring.
    [[gnu::always_inline]] inline constexpr int
    popcount64_licm(uint64_t x) noexcept
    {
        uint64_t const k3 = imm64(POPC_K[1]);
        x = x - ((x >> 1) & imm64(POPC_K[0]));
        x = (x & k3) + ((x >> 2) & k3);
        x = (x + (x >> 4)) & imm64(POPC_K[2]);
        return static_cast<int>((x * imm64(POPC_K[3])) >> 56);
    }
}

#define __builtin_popcount(x)                                                  \
    (::monad::bits::popcount64_licm(static_cast<::std::uint32_t>(x)))
#define __builtin_popcountl(x)                                                 \
    (::monad::bits::popcount64_licm(static_cast<::std::uint64_t>(x)))
#define __builtin_popcountll(x)                                                \
    (::monad::bits::popcount64_licm(static_cast<::std::uint64_t>(x)))
