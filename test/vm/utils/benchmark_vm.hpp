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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <string_view>
#include <utility>

namespace monad::vm::test
{
    /// Name of the VM mode in benchmark output. Deliberately not
    /// `VM::mode_to_string`: benchmark names are consumed by the comparison
    /// scripts and must stay stable.
    constexpr std::string_view impl_name(VM::Mode const mode) noexcept
    {
        switch (mode) {
        case VM::InterpreterOnly:
            return "interpreter";
        case VM::CompilerOnly:
            return "compiler";
        case VM::Dual:
            return "dual";
        }
        std::unreachable();
    }

    /// Put the final form of the varcode for `traits` in the VM's cache and
    /// return it, so that executing it never enters the compile path and a
    /// benchmark measures execution alone.
    ///
    /// The two modes need different steps because `execute_raw` consults the
    /// varcode's native code before it consults the VM mode. `cached_compile`
    /// always produces real native code regardless of mode, so using it in
    /// InterpreterOnly would make the "interpreter" run native code. The
    /// async path is the one that honours the mode: with async compilation
    /// disabled, the compile thread stores a null-entrypoint marker instead,
    /// which `execute_raw` reads as "interpret, and do not queue a compile
    /// job again".
    template <Traits traits>
    SharedVarcode prime_varcode_cache(
        VM &vm, bytes32_t const &code_hash, SharedIntercode const &icode)
    {
        if (auto const cached = vm.find_varcode(code_hash);
            cached && (*cached)->nativecode() != nullptr &&
            (*cached)->nativecode()->chain_id() == traits::id()) {
            return *cached;
        }
        if (vm.mode() == VM::CompilerOnly) {
            auto const ncode = vm.compiler().cached_compile<traits>(
                code_hash, icode, vm.compiler_config());
            // Fail loudly instead of silently benchmarking the interpreter
            // fallback.
            MONAD_ASSERT(ncode->entrypoint() != nullptr);
        }
        else {
            vm.compiler().async_compile<traits>(
                code_hash, icode, vm.compiler_config());
            vm.compiler().debug_wait_for_empty_queue();
        }
        return vm.find_varcode(code_hash).value();
    }
}
