// Copyright (C) 2026 Category Labs, Inc.
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

#ifdef MONAD_VM_COMPILER_OFFLINE
    #ifndef ASMJIT_NO_JIT
        #error "Symbolic runtime references must never be used by the JIT"
    #endif
    #include <category/core/assert.h>
    #include <cstdint>
    #include <map>
    #include <string_view>

namespace monad::vm::compiler::native
{
    // These are display-only addresses, never callable WASM function pointers.
    // Hash the source name so assembly is independent of compilation history.
    inline thread_local std::map<uint64_t, std::string_view> runtime_references;

    template <auto Function>
    auto runtime_reference(std::string_view name)
    {
        uint64_t address = 14695981039346656037ULL;
        for (char const c : name) {
            address =
                (address ^ static_cast<unsigned char>(c)) * 1099511628211ULL;
        }
        auto const [it, inserted] = runtime_references.emplace(address, name);
        MONAD_ASSERT(inserted || it->second == name);
        return reinterpret_cast<decltype(Function)>(address);
    }

    inline std::string_view runtime_reference_name(void *pointer)
    {
        return runtime_references.at(reinterpret_cast<uint64_t>(pointer));
    }
}

    #define MONAD_VM_RUNTIME_REFERENCE(f)                                      \
        ::monad::vm::compiler::native::runtime_reference<f>(#f)
#else
    #define MONAD_VM_RUNTIME_REFERENCE(f) (f)
#endif
