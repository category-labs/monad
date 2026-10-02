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

#include <evmc/evmc.h>

#ifdef __cplusplus
extern "C"
{
#endif

// Monad's in-tree EIP-2929 access status enum. This is a drop-in replacement
// for evmc's `evmc_access_status`: the enumerators mirror `evmc_access_status`
// 1:1 (same underlying integer values), which keeps the cold/warm comparisons
// numerically unchanged. The 1:1 correspondence is enforced by static_assert in
// access_status.cpp.
//
// The enum itself carries no evmc dependency. The only tie to evmc is the
// conversion function below, used solely by the test-only EvmcHostAdapter that
// serves evmc's C host interface to the spec VM; it — together with the
// <evmc/evmc.h> include — is removable together with that adapter.
enum monad_access_status
{
    MONAD_ACCESS_COLD = 0,
    MONAD_ACCESS_WARM = 1
};

// Convert monad_access_status to evmc's evmc_access_status. Needed only by the
// test-only EvmcHostAdapter (see the note above).
enum evmc_access_status to_evmc_access_status(enum monad_access_status status);

#ifdef __cplusplus
} // extern "C"
#endif
