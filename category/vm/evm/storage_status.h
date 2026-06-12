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

// Monad's in-tree EIP-1283/2200 storage status enum. This is a drop-in
// replacement for evmc's `evmc_storage_status`: the enumerators mirror
// `evmc_storage_status` 1:1 (same underlying integer values), which keeps the
// gas/refund table lookups in store_cost numerically unchanged. The 1:1
// correspondence is enforced by static_assert in storage_status.cpp.
//
// The enum itself carries no evmc dependency. The only tie to evmc is the
// conversion function below, which is needed solely at the remaining evmc host
// interface boundary (the EvmcHost overrides, whose return types are fixed by
// evmc::HostInterface); it — together with the <evmc/evmc.h> include — is
// removable in one step once the host interface is ported off evmc.
enum monad_storage_status
{
    MONAD_STORAGE_ASSIGNED = 0,
    MONAD_STORAGE_ADDED = 1,
    MONAD_STORAGE_DELETED = 2,
    MONAD_STORAGE_MODIFIED = 3,
    MONAD_STORAGE_DELETED_ADDED = 4,
    MONAD_STORAGE_MODIFIED_DELETED = 5,
    MONAD_STORAGE_DELETED_RESTORED = 6,
    MONAD_STORAGE_ADDED_DELETED = 7,
    MONAD_STORAGE_MODIFIED_RESTORED = 8
};

// Convert monad_storage_status to evmc's evmc_storage_status. Needed only at
// the remaining evmc host interface boundary (see the note above).
enum evmc_storage_status
to_evmc_storage_status(enum monad_storage_status status);

#ifdef __cplusplus
} // extern "C"
#endif
