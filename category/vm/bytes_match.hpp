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

#include <cstddef>
#include <cstdint>

namespace monad::vm
{
#if defined(MONAD_ZKVM_ZISK)
    // Compare N bytes using ZisK's DMA
    // comparator (CSR 0x814). The following instruction encodes the length.
    template <size_t N, size_t M>
    [[gnu::always_inline]] inline bool bytes_match(
        uint8_t const *const bytes, unsigned char const (&pattern)[M]) noexcept
    {
        static_assert(N <= M);
        uint64_t mismatch;
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "addi x0, %2, %5\n\t"
            ".option pop"
            : "=&r"(mismatch)
            : "r"(bytes),
              "r"(pattern),
              "m"(*reinterpret_cast<uint8_t const(*)[N]>(bytes)),
              "m"(pattern),
              "i"(N));
        return mismatch == 0;
    }

#endif
}
