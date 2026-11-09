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

#ifdef __cplusplus
extern "C"
{
#endif

// EIP-1283/2200 storage status; indexes the gas/refund tables in store_cost.
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

#ifdef __cplusplus
} // extern "C"
#endif
