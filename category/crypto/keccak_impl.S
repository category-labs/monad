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

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

#if defined(__x86_64__)
    #if defined(__AVX512F__)
        #include <crypto/sha/asm/keccak1600-avx512.S>
    #elif defined(__AVX2__)
        #include <crypto/sha/asm/keccak1600-avx2.S>
    #else
        #error avx2 or avx512 required
    #endif
#else
    #error unsupported arch
#endif
