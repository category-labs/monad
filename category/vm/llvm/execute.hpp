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

#include <category/vm/llvm/llvm_state.hpp>

#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

namespace monad::vm::llvm
{
    using namespace monad::vm::runtime;

    void execute(LLVMState &llvm, Context &, uint256_t *);
    std::shared_ptr<LLVMState>
    compile(evmc_revision rev, std::span<uint8_t const> code);
}
