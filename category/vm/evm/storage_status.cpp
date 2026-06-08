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

#include <category/vm/evm/storage_status.h>

#include <evmc/evmc.h>

#include <utility>

// Enforce the 1:1 correspondence with evmc_storage_status that makes the
// conversion below a value-preserving cast. If evmc ever renumbers a value,
// these fire.
#define MONAD_ASSERT_STORAGE_STATUS_EQ(status)                                 \
    static_assert(                                                             \
        std::to_underlying(MONAD_STORAGE_##status) ==                          \
        std::to_underlying(EVMC_STORAGE_##status))

MONAD_ASSERT_STORAGE_STATUS_EQ(ASSIGNED);
MONAD_ASSERT_STORAGE_STATUS_EQ(ADDED);
MONAD_ASSERT_STORAGE_STATUS_EQ(DELETED);
MONAD_ASSERT_STORAGE_STATUS_EQ(MODIFIED);
MONAD_ASSERT_STORAGE_STATUS_EQ(DELETED_ADDED);
MONAD_ASSERT_STORAGE_STATUS_EQ(MODIFIED_DELETED);
MONAD_ASSERT_STORAGE_STATUS_EQ(DELETED_RESTORED);
MONAD_ASSERT_STORAGE_STATUS_EQ(ADDED_DELETED);
MONAD_ASSERT_STORAGE_STATUS_EQ(MODIFIED_RESTORED);

#undef MONAD_ASSERT_STORAGE_STATUS_EQ

// This is a value-preserving cast: monad_storage_status mirrors
// evmc_storage_status 1:1, enforced by the static_asserts above. C linkage
// matches the declaration in storage_status.h.
evmc_storage_status to_evmc_storage_status(monad_storage_status const status)
{
    return static_cast<evmc_storage_status>(std::to_underlying(status));
}
