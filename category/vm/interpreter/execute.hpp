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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/runtime/types.hpp>

namespace monad::vm::interpreter
{
    /// `stack_ptr` must address at least 1025 slots, as `EvmStackAllocator`
    /// provides; slot 0 is reserved as the empty-stack marker.
    template <Traits traits>
    void execute(runtime::Context &, Intercode const &, uint256_t *stack_ptr);
}
