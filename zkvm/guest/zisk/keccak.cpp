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

// The ZisK guest's Keccak-256 entry points. Inline CSR instructions avoid a
// call and return around each backend function.

#include <category/core/config.hpp>
#include <category/crypto/keccak.h>
#include <zkvm/guest/keccak_accel.hpp>

#include <cstddef>
#include <cstdint>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct ZiskKeccakBackend
{
    // Keccak-f[1600] on `state`, in place (CSR 0x800). The memory clobber
    // tells the compiler that the instruction reads and writes memory.
    [[gnu::always_inline]] static void keccakf(uint64_t state[25]) noexcept
    {
        asm volatile("csrs 0x800, %0" : : "r"(state) : "memory");
    }

    // Fcalls push a value via 0x8F0 or a 25-word state via 0x8F8, invoke
    // through 0x8C0, and read the result at 0xFFE. The "r" constraint keeps
    // even zero values out of x0, which ZisK treats as a no-op instead of a
    // push.

    [[gnu::always_inline]] static uint64_t
    get_index(uint64_t const state[25]) noexcept
    {
        uint64_t index;
        asm volatile("csrs 0x8F8, %[state]\n\t" // one parameter: 25 words
                     "csrwi 0x8C0, 25\n\t" // FCALL_GET_KECCAKF_CACHE_INDEX_ID
                     "csrr %[index], 0xFFE"
                     : [index] "=&r"(index)
                     : [state] "r"(state)
                     : "memory");
        return index;
    }

    [[gnu::always_inline]] static void set_index(uint64_t const index) noexcept
    {
        asm volatile("csrs 0x8F0, %0\n\t" // one parameter, by value
                     "csrwi 0x8C0, 24" // FCALL_SET_KECCAKF_CACHE_INDEX_ID
                     :
                     : "r"(index)
                     : "memory");
    }
};

MONAD_ANONYMOUS_NAMESPACE_END

void monad_keccak256(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    monad::keccak256_memo<monad::ZiskKeccakBackend>(
        input, input_length, output);
}

void monad_keccak256_nomemo(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    monad::keccak256_nomemo<monad::ZiskKeccakBackend>(
        input, input_length, output);
}
