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

namespace monad::vm::aot
{
    struct Entry
    {
        uint64_t hash[4];
        size_t size;
        interpreter::core_loop_fn_t fn;
    };

    // The compiled function for a code of the revision the table was written
    // for, or null.
    interpreter::core_loop_fn_t
    find(bytes32_t const &code_hash, size_t code_size) noexcept;
}
