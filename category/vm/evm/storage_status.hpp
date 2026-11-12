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

#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

// EIP-1283/2200 storage status; indexes the gas/refund tables in
// store_cost.
enum class StorageStatus
{
    Assigned = 0,
    Added = 1,
    Deleted = 2,
    Modified = 3,
    DeletedAdded = 4,
    ModifiedDeleted = 5,
    DeletedRestored = 6,
    AddedDeleted = 7,
    ModifiedRestored = 8
};

MONAD_NAMESPACE_END
