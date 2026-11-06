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
    constexpr std::size_t jumpdest_word_count(std::size_t const code_size)
    {
        return (code_size + 63) / 64;
    }

    // The scalar scan: the production path on targets without AVX2 (including
    // the RISC-V zkVM guest), and the reference the AVX2 kernel is tested
    // against. ORs a bit into `bits` for each JUMPDEST, so `bits` must be
    // zeroed.
    void find_jumpdests_scalar(
        std::uint8_t const *code, std::size_t code_size, std::uint64_t *bits);

#if defined(__AVX2__)
    // Same bits as find_jumpdests_scalar, into zeroed `bits` (the final
    // 32-byte block's write may leave a word's high half untouched). Reads
    // `code` in 32-byte steps, so it needs >= 31 bytes of zero padding after
    // code_size.
    void find_jumpdests_avx2(
        std::uint8_t const *code, std::size_t code_size, std::uint64_t *bits);
#endif
}
