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

#pragma once

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/bin.hpp>

#include <asmjit/x86.h>

#include <evmc/evmc.h>

#include <memory>
#include <span>

namespace monad::vm::compiler::native
{
    /**
     * Compile the given contract and add it to JitRuntime.
     */
    std::shared_ptr<Nativecode> compile(
        asmjit::JitRuntime &rt, std::uint8_t const *contract_code,
        interpreter::code_size_t contract_code_size, evmc_revision rev,
        CompilerConfig const & = {});

    /**
     * Compile given IR and add it to the JitRuntime.
     */
    std::shared_ptr<Nativecode> compile_basic_blocks(
        evmc_revision rev, asmjit::JitRuntime &rt,
        basic_blocks::BasicBlocksIR const &ir, CompilerConfig const & = {});

    /**
     * Upper bound on (estimated) native contract size in bytes.
     */
    constexpr native_code_size_t max_code_size(
        interpreter::code_size_t offset,
        interpreter::code_size_t bytecode_size) noexcept
    {
        // A contract will be compiled asynchronously after the accumulated
        // execution gas cost of interpretation reaches this threshold. If
        // byte code size is 128kB, then the interpreter will need to use
        // more than 4 million gas on this contract before it will be
        // compiled, when `offset` is zero. There is a theoretical hard
        // upper bound on native code size to ensure that the emitter
        // will not overflow relative x86 memory addressing offsets.
        return offset + shl<5>(bytecode_size);
    }
}
