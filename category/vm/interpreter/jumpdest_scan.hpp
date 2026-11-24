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

namespace monad::vm::interpreter::detail
{
    constexpr size_t jumpdest_word_count(size_t const code_size)
    {
        return (code_size + 63) / 64;
    }

    // Used on targets without AVX2, including the RISC-V zkVM guest. ORs a
    // bit into `bits` for each JUMPDEST, so `bits` must start zeroed.
    void find_jumpdests_scalar(
        uint8_t const *code, size_t code_size, uint64_t *bits);

    // Bytes of zero padding the AVX2 scan reads past the code.
    inline constexpr size_t avx2_scan_padding = 31;

#if defined(__AVX2__)
    // Same bits as find_jumpdests_scalar, and copies the code from `src` into
    // `dst`; `bits` must start zeroed. Reads `src` only within code_size;
    // `dst` needs avx2_scan_padding zero bytes after code_size and must not
    // overlap `src`.
    void copy_and_find_jumpdests_avx2(
        uint8_t const *src, uint8_t *dst, size_t code_size, uint64_t *bits);
#endif
}
