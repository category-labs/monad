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

// The x86 runner's Keccak-256 entry points: the guest's sponge over aws-lc's
// permutation, with no executor.

#include <category/core/config.hpp>
#include <category/crypto/keccak.h>
#include <zkvm/guest/keccak_accel.hpp>

#include <cstddef>
#include <cstdint>

// aws-lc's Keccak-f[1600] (crypto/fipsmodule/sha/keccak1600.c), which it
// declares only in an internal header. The root CMakeLists.txt prefixes
// aws-lc's symbols with AWS_.
extern "C" void AWS_KeccakF1600(uint64_t state[5][5]);

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct X86KeccakBackend
{
    // Keccak-f[1600] on `state`, in place: the same permutation as ZisK's
    // precompile.
    static void keccakf(uint64_t state[25])
    {
        AWS_KeccakF1600(reinterpret_cast<uint64_t(*)[5]>(state));
    }

    // No executor runs alongside the process, so every lookup misses.
    static uint64_t get_index(uint64_t const * /*state*/)
    {
        return KECCAKF_INDEX_NOT_FOUND;
    }

    static void set_index(uint64_t /*index*/) {}
};

MONAD_ANONYMOUS_NAMESPACE_END

void monad_keccak256(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    monad::keccak256_memo<monad::X86KeccakBackend>(input, input_length, output);
}

void monad_keccak256_nomemo(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    monad::keccak256_nomemo<monad::X86KeccakBackend>(
        input, input_length, output);
}
