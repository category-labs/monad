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

// Codes compiled ahead of time into the ZisK guest, by code hash: a frame
// whose code is one of them runs its function under the interpreter's
// trampoline instead of the interpreter (zkvm/category/vm/vm.hpp).

#pragma once

#include <category/core/bytes.hpp>
#include <category/vm/interpreter/trampoline.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>

namespace monad::vm::aot
{
    struct Entry
    {
        uint64_t hash[4];
        size_t size;
        interpreter::core_loop_fn_t fn;
        Entry const *next;
    };

    // The entries by the first byte of their code hash: a frame whose code
    // is not among them reads one empty slot.
    extern Entry const *const table[256];

    // The compiled function for a code of the revision the table was written
    // for, or null.
    [[gnu::always_inline]] inline interpreter::core_loop_fn_t
    find(bytes32_t const &code_hash, size_t const code_size) noexcept
    {
        for (Entry const *e = table[code_hash.bytes[0]]; e != nullptr;
             e = e->next) {
            if (e->size == code_size &&
                std::memcmp(e->hash, code_hash.bytes, 32) == 0) {
                return e->fn;
            }
        }
        return nullptr;
    }
}
