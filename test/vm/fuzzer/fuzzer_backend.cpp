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

#include "fuzzer_backend.hpp"

#include <category/core/assert.h>
#include <category/vm/evm/delegation.hpp>

#include <cstdint>
#include <vector>

namespace monad::vm::fuzzing
{
    Address FuzzerBackend::deploy_delegated(
        Address const &from, Address const &delegatee)
    {
        auto const prefix = vm::evm::delegation_indicator_prefix();
        std::vector<uint8_t> code(prefix.begin(), prefix.end());
        code.append_range(delegatee.bytes);
        MONAD_ASSERT(code.size() == 23);
        return deploy(from, code);
    }
}
