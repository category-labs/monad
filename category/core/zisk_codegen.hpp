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

// Workarounds for what the guest's compiler emits, where the fix is a property
// of the generated code rather than of the algorithm.

namespace monad
{
    // Zero-extend a byte before storing it.
    //
    // ZisK prices an unaligned one-byte store at 66 cells when the source
    // register holds a zero-extended byte and 193 when it does not -- a
    // 127-cell surcharge that depends on the REGISTER's upper bits, not on the
    // address and not on any property of the memory. gcc materialises a QImode
    // constant >= 0x80 in its SIGN-extended form (`li a3,-96` for 0xa0), so
    // every store of a high byte constant pays it, and RLP prefixes are all
    // high.
    //
    // An empty asm barrier on a 64-bit copy of the value forces `li a3,160`
    // instead, and costs nothing: gcc still hoists the constant out of the loop
    // it feeds.
    //
    // Guarded, because on a real CPU the barrier costs an instruction and buys
    // nothing: there, a byte store is a byte store.
    [[gnu::always_inline]] inline unsigned char zx(unsigned long v) noexcept
    {
#if defined(MONAD_ZKVM_ZISK)
        asm("" : "+r"(v));
#endif
        return static_cast<unsigned char>(v);
    }
}
