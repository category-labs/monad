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

#include <category/vm/core/assert.h>

#include <evmc/evmc.hpp>

namespace monad::vm::fuzzing
{
    inline uint8_t num_precompiles(evmc_revision rev)
    {
        if (rev <= EVMC_SPURIOUS_DRAGON) {
            return 4;
        }
        else if (rev <= EVMC_PETERSBURG) {
            return 8;
        }
        else if (rev <= EVMC_SHANGHAI) {
            return 9;
        }
        else if (rev == EVMC_CANCUN) {
            return 10;
        }
        else if (rev == EVMC_PRAGUE) {
            return 17;
        }
        else if (rev == EVMC_OSAKA) {
            // TODO(BSC): handle discontinuous precompiles
            MONAD_VM_ASSERT(false);
        }
        else {
            MONAD_VM_ASSERT(false);
        }
    }
}
